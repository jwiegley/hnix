{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}


module Nix.Standard where

import           Prelude hiding                 ( force )
import           Control.Comonad                ( Comonad )
import           Control.Comonad.Env            ( ComonadEnv )
import           Control.Monad.Catch            ( MonadThrow
                                                , MonadCatch
                                                , MonadMask
                                                )
#if !MIN_VERSION_base(4,13,0)
import           Control.Monad.Fail             ( MonadFail )
#endif
import           Control.Monad.Free             ( Free(Pure, Free) )
import           Control.Monad.Reader           ( MonadFix )
import           Control.Monad.Ref              ( MonadRef(newRef)
                                                , MonadAtomicRef
                                                )
import qualified Text.Show
import           Nix.Cited
import           Nix.Cited.Basic
import           Nix.Context
import           Nix.Effects
import           Nix.Effects.Basic
import           Nix.Effects.Derivation
import           Nix.Expr.Types.Annotated
import           Nix.Fresh
import           Nix.Fresh.Basic
import           Nix.Options
import           Nix.Render
import           Nix.Scope
import           Nix.Thunk
import           Nix.Thunk.Basic
import           Nix.Utils                      ( free )
import           Nix.Utils.Fix1                 ( Fix1T(Fix1T) )
import           Nix.Value
import           Nix.Value.Monad


newtype StdCited m a =
  StdCited
    { _stdCited :: Cited (StdThunk m) (StdCited m) m a }
  deriving
    ( Generic
    , Typeable
    , Functor
    , Applicative
    , Foldable
    , Traversable
    , Comonad
    , ComonadEnv [Provenance m (StdValue m)]
    )

newtype StdThunk (m :: Type -> Type) =
  StdThunk
    { _stdThunk :: StdCited m (NThunkF m (StdValue m)) }

type StdValue' m = NValue' (StdThunk m) (StdCited m) m (StdValue m)
type StdValue m = NValue (StdThunk m) (StdCited m) m

instance Show (StdThunk m) where
  show _ = toString thunkStubText

instance HasCitations1 m (StdValue m) (StdCited m) where
  citations1 (StdCited c) = citations1 c
  addProvenance1 x (StdCited c) = StdCited $ addProvenance1 x c

instance HasCitations m (StdValue m) (StdThunk m) where
  citations (StdThunk c) = citations1 c
  addProvenance x (StdThunk c) = StdThunk $ addProvenance1 x c

instance MonadReader (Context m (StdValue m)) m => Scoped (StdValue m) m where
  currentScopes = currentScopesReader
  clearScopes   = clearScopesReader @m @(StdValue m)
  pushScopes    = pushScopesReader
  lookupVar     = lookupVarReader

instance
  ( MonadFix m
  , MonadFile m
  , MonadCatch m
  , MonadEnv m
  , MonadPaths m
  , MonadExec m
  , MonadHttp m
  , MonadInstantiate m
  , MonadIntrospect m
  , MonadPlus m
  , MonadPutStr m
  , MonadStore m
  , MonadAtomicRef m
  , Typeable m
  , Scoped (StdValue m) m
  , MonadReader (Context m (StdValue m)) m
  , MonadState (HashMap FilePath NExprLoc, HashMap Text Text) m
  , MonadDataErrorContext (StdThunk m) (StdCited m) m
  , MonadThunk (StdThunk m) m (StdValue m)
  , MonadValue (StdValue m) m
  )
  => MonadEffects (StdThunk m) (StdCited m) m where
  makeAbsolutePath = defaultMakeAbsolutePath
  findEnvPath      = defaultFindEnvPath
  findPath         = defaultFindPath
  importPath       = defaultImportPath
  pathToDefaultNix = defaultPathToDefaultNix
  derivationStrict = defaultDerivationStrict
  traceEffect      = defaultTraceEffect

instance
  ( Typeable       m
  , MonadThunkId   m
  , MonadAtomicRef m
  , MonadCatch     m
  , MonadReader (Context m (StdValue m)) m
  )
  => MonadThunk (StdThunk m) m (StdValue m) where

  thunkId
    :: StdThunk m
    -> ThunkId  m
  thunkId = thunkId . _stdCited . _stdThunk
  {-# inline thunkId #-}

  thunk
    :: m (StdValue m)
    -> m (StdThunk m)
  thunk = fmap (StdThunk . StdCited) . thunk

  query
    :: m (StdValue m)
    ->    StdThunk m
    -> m (StdValue m)
  query b = query b . _stdCited . _stdThunk

  force
    ::    StdThunk m
    -> m (StdValue m)
  force = force . _stdCited . _stdThunk

  forceEff
    ::    StdThunk m
    -> m (StdValue m)
  forceEff = forceEff . _stdCited . _stdThunk

  further
    ::    StdThunk m
    -> m (StdThunk m)
  further = fmap (StdThunk . StdCited) . further . _stdCited . _stdThunk


-- * @instance MonadThunkF@ (Kleisli functor HOFs)

-- Please do not use MonadThunkF instances to define MonadThunk. as MonadThunk uses specialized functions.
instance
  ( Typeable       m
  , MonadThunkId   m
  , MonadAtomicRef m
  , MonadCatch     m
  , MonadReader (Context m (StdValue m)) m
  )
  => MonadThunkF (StdThunk m) m (StdValue m) where

  queryF
    :: ( StdValue m
       -> m r
       )
    -> m r
    -> StdThunk m
    -> m r
  queryF k b = queryF k b . _stdCited . _stdThunk

  forceF
    :: ( StdValue m
       -> m r
       )
    -> StdThunk m
    -> m r
  forceF k = forceF k . _stdCited . _stdThunk

  forceEffF
    :: ( StdValue m
       -> m r
       )
    -> StdThunk m
    -> m r
  forceEffF k = forceEffF k . _stdCited . _stdThunk

  furtherF
    :: ( m (StdValue m)
       -> m (StdValue m)
       )
    ->    StdThunk m
    -> m (StdThunk m)
  furtherF k = fmap (StdThunk . StdCited) . furtherF k . _stdCited . _stdThunk


-- * @instance MonadValue (StdValue m) m@

instance
  ( MonadAtomicRef m
  , MonadCatch m
  , Typeable m
  , MonadReader (Context m (StdValue m)) m
  , MonadThunkId m
  )
  => MonadValue (StdValue m) m where

  defer
    :: m (StdValue m)
    -> m (StdValue m)
  defer = fmap pure . thunk

  demand
    :: StdValue m
    -> m (StdValue m)
  demand v =
    free
      (demand <=< force)
      (const $ pure v)
      v

  inform
    :: StdValue m
    -> m (StdValue m)
  inform (Pure t) = Pure <$> further t
  inform (Free v) = Free <$> bindNValue' id inform v


-- * @instance MonadValueF (StdValue m) m@

instance
  ( MonadAtomicRef m
  , MonadCatch m
  , Typeable m
  , MonadReader (Context m (StdValue m)) m
  , MonadThunkId m
  )
  => MonadValueF (StdValue m) m where

  demandF
    :: ( StdValue m
      -> m r
      )
    -> StdValue m
    -> m r
  demandF f = f <=< demand

  informF
    :: ( m (StdValue m)
      -> m (StdValue m)
      )
    -> StdValue m
    -> m (StdValue m)
  informF f = f . inform


{------------------------------------------------------------------------}

-- jww (2019-03-22): NYI
-- whileForcingThunk
--   :: forall t f m s e r . (Exception s, Convertible e t f m) => s -> m r -> m r
-- whileForcingThunk frame =
--   withFrame Debug (ForcingThunk @t @f @m) . withFrame Debug frame

newtype StandardTF r m a
  = StandardTF
      (ReaderT
        (Context r (StdValue r))
        (StateT (HashMap FilePath NExprLoc, HashMap Text Text) m)
        a
      )
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadFail
    , MonadPlus
    , MonadFix
    , MonadIO
    , MonadCatch
    , MonadThrow
    , MonadMask
    , MonadReader (Context r (StdValue r))
    , MonadState (HashMap FilePath NExprLoc, HashMap Text Text)
    )

instance MonadTrans (StandardTF r) where
  lift = StandardTF . lift . lift
  {-# inline lift #-}

instance (MonadPutStr r, MonadPutStr m)
  => MonadPutStr (StandardTF r m)
instance (MonadHttp r, MonadHttp m)
  => MonadHttp (StandardTF r m)
instance (MonadEnv r, MonadEnv m)
  => MonadEnv (StandardTF r m)
instance (MonadPaths r, MonadPaths m)
  => MonadPaths (StandardTF r m)
instance (MonadInstantiate r, MonadInstantiate m)
  => MonadInstantiate (StandardTF r m)
instance (MonadExec r, MonadExec m)
  => MonadExec (StandardTF r m)
instance (MonadIntrospect r, MonadIntrospect m)
  => MonadIntrospect (StandardTF r m)

---------------------------------------------------------------------------------

type StandardT m = Fix1T StandardTF m

instance MonadTrans (Fix1T StandardTF) where
  lift = Fix1T . lift

instance MonadThunkId m
  => MonadThunkId (StandardT m) where

  type ThunkId (StandardT m) = ThunkId m

mkStandardT
  :: ReaderT
      (Context (StandardT m) (StdValue (StandardT m)))
      (StateT (HashMap FilePath NExprLoc, HashMap Text Text) m)
      a
  -> StandardT m a
mkStandardT = coerce

runStandardT
  :: StandardT m a
  -> ReaderT
      (Context (StandardT m) (StdValue (StandardT m)))
      (StateT (HashMap FilePath NExprLoc, HashMap Text Text) m)
      a
runStandardT = coerce

runWithBasicEffects
  :: (MonadIO m, MonadAtomicRef m)
  => Options
  -> StandardT (StdIdT m) a
  -> m a
runWithBasicEffects opts =
  go . (`evalStateT` mempty) . (`runReaderT` newContext opts) . runStandardT
 where
  go action = do
    i <- newRef (1 :: Int)
    runFreshIdT i action

runWithBasicEffectsIO :: Options -> StandardT (StdIdT IO) a -> IO a
runWithBasicEffectsIO = runWithBasicEffects
