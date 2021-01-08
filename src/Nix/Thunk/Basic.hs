{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Nix.Thunk.Basic (ThunkT (..), runThunkT, NThunkF (..), Deferred (..)) where

import           Control.Exception       hiding ( catch )
import           Control.Monad.Catch
import           Control.Monad.Fail
import           Control.Monad.Reader
import           Control.Monad.State

import           Nix.Effects
import           Nix.Thunk
import           Nix.Var
import           Nix.Thunk.StableId
import           Nix.Fresh.Stable
import           Control.Applicative
import           Control.Monad.Ref
import Data.Typeable
#ifdef MIN_VERSION_haskeline
import System.Console.Haskeline.MonadException hiding(catch)
#endif

newtype ThunkT v m a = ThunkT { unThunkT :: FreshStableIdT m a }
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadPlus
    , MonadFail
    , MonadFix
    , MonadRef
    , MonadAtomicRef
    , MonadIO
    , MonadCatch
    , MonadThrow
#ifdef MIN_VERSION_haskeline
    , MonadException
#endif
    , MonadMask
    , MonadStore
    )

deriving instance MonadState s m => MonadState s (ThunkT v m)

instance MonadReader r m => MonadReader r (ThunkT v m) where
  ask = lift ask
  local f = liftWrap $ local f
  reader = lift . reader

runThunkT :: Monad m => ThunkT v m a -> StableId -> m a
runThunkT (ThunkT a) root = runFreshStableIdT root a

instance MonadTrans (ThunkT v) where
  lift = ThunkT . lift

instance MonadTransWrap (ThunkT v) where
  liftWrap f (ThunkT a) = ThunkT $ liftWrap f a

data Deferred m v = Deferred (m v) | Computed v
    deriving (Functor, Foldable, Traversable)

-- | The type of very basic thunks
data NThunkF m v
    = Thunk StableId (Var m Bool) (Var m (Deferred m v))

instance Eq (NThunkF m v) where
  Thunk x _ _ == Thunk y _ _ = x == y

instance Ord (NThunkF m v) where
  Thunk x _ _ `compare` Thunk y _ _ = x `compare` y

instance Show (NThunkF m v) where
  show (Thunk tid _ _) = "<thunk " <> show tid <> ">"

instance (Typeable v, Typeable m, MonadAtomicRef m, MonadCatch m)
  => MonadThunk (ThunkT v m) where
  type Thunk (ThunkT v m) = NThunkF m v
  type ThunkValue (ThunkT v m) = v
  thunk = buildThunk
  queryM = queryThunk
  force = forceThunk
  forceEff = forceEffects
  further t f = thunk $ f $ force t pure

buildThunk :: MonadRef m => ThunkT v m v -> ThunkT v m (NThunkF m v)
buildThunk (ThunkT action) = ThunkT $ do
  freshThunkId <- freshId
  Thunk freshThunkId <$> newVar False <*> newVar (Deferred $ runFreshStableIdT freshThunkId action)

queryThunk :: MonadVar m => NThunkF m v -> ThunkT v m a -> (v -> ThunkT v m a) -> ThunkT v m a
queryThunk (Thunk _ active ref) n k = do
  nowActive <- atomicModifyVar active (True, )
  if nowActive
    then n
    else do
      eres <- readVar ref
      res  <- case eres of
        Computed v -> k v
        _          -> n
      _ <- atomicModifyVar active (False, )
      pure res

forceThunk
  :: forall m v a
   . (MonadVar m, MonadThrow m, MonadCatch m, Show StableId)
  => NThunkF m v
  -> (v -> ThunkT v m a)
  -> ThunkT v m a
forceThunk (Thunk n active ref) k = do
  eres <- readVar ref
  case eres of
    Computed v      -> k v
    Deferred action -> do
      nowActive <- atomicModifyVar active (True, )
      if nowActive
        then throwM $ ThunkLoop $ show n
        else do
          v <- catch (ThunkT $ lift action) $ \(e :: SomeException) -> do
            _ <- atomicModifyVar active (False, )
            throwM e
          _ <- atomicModifyVar active (False, )
          writeVar ref (Computed v)
          k v

forceEffects :: MonadVar m => NThunkF m v -> (v -> ThunkT v m r) -> ThunkT v m r
forceEffects (Thunk _ active ref) k = do
  nowActive <- atomicModifyVar active (True, )
  if nowActive
    then pure $ error "Loop detected"
    else do
      eres <- readVar ref
      case eres of
        Computed v      -> k v
        Deferred action -> do
          v <- ThunkT $ lift action
          writeVar ref (Computed v)
          _ <- atomicModifyVar active (False, )
          k v

{-
--[ryantrinkle] I'm worried about what impact this will have on the way withRootId works
furtherThunk :: MonadVar m => NThunkF m v -> (m v -> m v) -> m (NThunkF m v)
furtherThunk t@(Thunk _ _ ref) k = do
  _ <- atomicModifyVar ref $ \x -> case x of
    Computed _ -> (x, x)
    Deferred d -> (Deferred (k d), x)
  pure t
-}
