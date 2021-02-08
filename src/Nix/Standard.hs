{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Nix.Standard where

import           Control.Applicative
import           Control.Monad.Catch     hiding ( catchJust )
#if !MIN_VERSION_base(4,13,0)
import           Control.Monad.Fail             ( MonadFail )
#endif
import           Control.Monad.Free
import           Control.Monad.Reader
import           Control.Monad.Ref
import           Control.Monad.State
import           Data.Coerce
import           Data.Functor.Identity
import           Data.HashMap.Lazy              ( HashMap )
import           Data.Text                      ( Text )
import           Data.Typeable
import           Nix.Cited
import           Nix.Context
import           Nix.Effects
import           Nix.Effects.Basic
import           Nix.Effects.Derivation
import           Nix.Expr.Types.Annotated
import           Nix.Thunk.StableId
import           Nix.Thunk.Basic
import           Nix.Options
import           Nix.Render
import           Nix.Scope
import           Nix.Scope.Basic
import           Nix.Thunk
import           Nix.Utils.Fix1
import           Nix.Value
import           Nix.Value.Monad

-- All of the following type classes defer to the underlying 'm'.

deriving instance MonadPutStr (t (Fix1 t)) => MonadPutStr (Fix1 t)
deriving instance MonadHttp (t (Fix1 t)) => MonadHttp (Fix1 t)
deriving instance MonadEnv (t (Fix1 t)) => MonadEnv (Fix1 t)
deriving instance MonadPaths (t (Fix1 t)) => MonadPaths (Fix1 t)
deriving instance MonadInstantiate (t (Fix1 t)) => MonadInstantiate (Fix1 t)
deriving instance MonadExec (t (Fix1 t)) => MonadExec (Fix1 t)
deriving instance MonadIntrospect (t (Fix1 t)) => MonadIntrospect (Fix1 t)

deriving instance MonadEnv (t (Fix1T t m) m) => MonadEnv (Fix1T t m)
deriving instance MonadExec (t (Fix1T t m) m) => MonadExec (Fix1T t m)
deriving instance MonadFile (t (Fix1T t m) m) => MonadFile (Fix1T t m)
deriving instance MonadHttp (t (Fix1T t m) m) => MonadHttp (Fix1T t m)
deriving instance MonadInstantiate (t (Fix1T t m) m) => MonadInstantiate (Fix1T t m)
deriving instance MonadIntrospect (t (Fix1T t m) m) => MonadIntrospect (Fix1T t m)
deriving instance MonadPaths (t (Fix1T t m) m) => MonadPaths (Fix1T t m)
deriving instance MonadPutStr (t (Fix1T t m) m) => MonadPutStr (Fix1T t m)
deriving instance MonadStore (t (Fix1T t m) m) => MonadStore (Fix1T t m)
deriving instance MonadThunk (t (Fix1T t m) m) => MonadThunk (Fix1T t m)
deriving instance Scoped r a (t (Fix1T t m) m) => Scoped r a (Fix1T t m)

type MonadFix1T t m = (MonadTrans (Fix1T t), Monad (t (Fix1T t m) m))

instance (MonadFix1T t m, MonadRef m) => MonadRef (Fix1T t m) where
  type Ref (Fix1T t m) = Ref m
  newRef  = lift . newRef
  readRef = lift . readRef
  writeRef r = lift . writeRef r

instance (MonadFix1T t m, MonadAtomicRef m) => MonadAtomicRef (Fix1T t m) where
  atomicModifyRef r = lift . atomicModifyRef r

---------------------------------------------------------------------------------

instance MonadFile m => MonadFile (StandardTF r m)
instance ( MonadFix m
         , MonadFile m
         , MonadCatch m
         , MonadEnv m
         , MonadExec m
         , MonadHttp m
         , MonadInstantiate m
         , MonadIntrospect m
         , MonadPlus m
         , MonadPutStr m
         , MonadStore m
         , MonadAtomicRef m
         , Typeable m
         , MonadPaths m
         )
  => MonadEffects Identity (StandardT m) where
  makeAbsolutePath = defaultMakeAbsolutePath
  findEnvPath      = defaultFindEnvPath
  findPath         = defaultFindPath
  importPath       = defaultImportPath
  pathToDefaultNix = defaultPathToDefaultNix
  derivationStrict = defaultDerivationStrict
  traceEffect      = defaultTraceEffect

{------------------------------------------------------------------------}

-- jww (2019-03-22): NYI
-- whileForcingThunk
--   :: forall t f m s e r . (Exception s, Convertible e t f m) => s -> m r -> m r
-- whileForcingThunk frame =
--   withFrame Debug (ForcingThunk @t @f @m) . withFrame Debug frame

type StandardTFInner r m = ScopeT (NValue Identity r) r
  (ThunkT (NValue Identity r) --TODO: What should this `Identity` be? Probably (StdCited ...)
    (ReaderT Context
      (StateT (HashMap FilePath NExprLoc, HashMap Text Text) m)))

newtype StandardTF r m a
  = StandardTF { unStandardTF :: StandardTFInner r m a }
  deriving
    ( Applicative
    , Alternative
    , Monad
    , MonadFail
    , MonadPlus
    , MonadFix
    , MonadIO
    , MonadCatch
    , MonadThrow
    , MonadMask
    , MonadReader Context
    , MonadState (HashMap FilePath NExprLoc, HashMap Text Text)
    , MonadStore
    )

deriving instance (Monad m, Monad r, Thunk r ~ StdThunk r m) => Scoped r (Free (NValue' Identity r) (StdThunk r m)) (StandardTF r m)

deriving instance Functor m => Functor (StandardTF r m)

instance MonadTrans (StandardTF r) where
  lift = StandardTF . lift . lift . lift . lift

instance MonadTransWrap (StandardTF r) where
  liftWrap f (StandardTF a) = StandardTF $ liftWrap (liftWrap (liftWrap (liftWrap f))) a

instance (MonadPutStr m) => MonadPutStr (StandardTF r m)
instance (MonadHttp m) => MonadHttp (StandardTF r m)
instance (MonadEnv m) => MonadEnv (StandardTF r m)
instance (MonadInstantiate m) => MonadInstantiate (StandardTF r m)
instance (MonadExec m) => MonadExec (StandardTF r m)
instance (MonadIntrospect m) => MonadIntrospect (StandardTF r m)

instance ( Monad m
         , Typeable r
         , Typeable (Thunk r)
         , Typeable m
         , MonadAtomicRef m
         , MonadCatch m
         ) => MonadThunk (StandardTF r m) where
  type Thunk (StandardTF r m) = StdThunk r m
  type ThunkValue (StandardTF r m) = StdValue r
  thunk v = StandardTF $ StdThunk <$> thunk (unStandardTF v)
  queryM = coerce $ queryM @(StandardTFInner r m)
  force = coerce $ force @(StandardTFInner r m)
  forceEff = coerce $ forceEff @(StandardTFInner r m)
  further t f = fmap StdThunk $ StandardTF $ further (unStdThunk t) $ unStandardTF . f . StandardTF

newtype StdThunk r m = StdThunk { unStdThunk :: Thunk (StandardTFInner r m) }
  deriving (Eq, Ord, Show, Typeable)

type StdValue r = NValue Identity r

instance MonadPaths m => MonadPaths (StandardTF r m)

instance ( Monad m
         , Typeable m
         , MonadAtomicRef m
         , MonadCatch m
         ) => MonadValue (Free (NValue' Identity (StandardT m)) (StdThunk (StandardT m) m)) (StandardT m) where
  defer = fmap pure . thunk

  demand (Pure v) f = force v (`demand` f)
  demand (Free v) f = f (Free v)

  inform (Pure t) f = Pure <$> further t f
  inform (Free v) f = Free <$> bindNValue' id (`inform` f) v

--TODO
instance HasCitations m' v (StdThunk r m) where
  citations _ = []
  addProvenance _ = id

instance HasCitations1 m v Identity where
  citations1 _ = []
  addProvenance1 _ = id

---------------------------------------------------------------------------------

type StandardT m = Fix1T StandardTF m

instance (forall m. MonadTrans (t (Fix1T t m))) => MonadTrans (Fix1T t) where
  lift = Fix1T . lift

mkStandardT
  :: StandardTFInner (Fix1T StandardTF m) m a
  -> StandardT m a
mkStandardT = Fix1T . StandardTF

runStandardT
  :: StandardT m a
  -> StandardTFInner (Fix1T StandardTF m) m a
runStandardT (Fix1T (StandardTF m)) = m

runWithBasicEffects
  :: (MonadIO m, MonadAtomicRef m) => Options -> StandardT m a -> m a
runWithBasicEffects opts =
  (`evalStateT` mempty) . (`runReaderT` newContext opts) . (`runThunkT` nil) . (`runScopeT` mempty) . runStandardT

runWithBasicEffectsIO :: Options -> StandardT IO a -> IO a
runWithBasicEffectsIO = runWithBasicEffects
