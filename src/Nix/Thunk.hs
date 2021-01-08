{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Nix.Thunk where

import           Control.Exception              ( Exception )
import           Control.Monad.Except
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Writer
import           Data.Typeable                  ( Typeable )

class MonadTransWrap t where
  --TODO: Can we enforce that the resulting function is as linear as the provided one?
  liftWrap :: Monad m => (forall x. m x -> m x) -> t m a -> t m a

instance MonadTransWrap (ReaderT s) where
  liftWrap f a = do
    env <- ask
    lift $ f $ runReaderT a env

instance Monoid w => MonadTransWrap (WriterT w) where
  liftWrap f a = do
    (result, w) <- lift $ f $ runWriterT a
    tell w
    pure result

instance MonadTransWrap (ExceptT e) where
  liftWrap f a = do
    lift (f $ runExceptT a) >>= \case
      Left e -> throwError e
      Right result -> pure result

instance MonadTransWrap (StateT s) where
  liftWrap f a = do
    old <- get
    (result, new) <- lift $ f $ runStateT a old
    put new
    pure result

class ( Monad m
      , Eq (Thunk m)
      , Ord (Thunk m)
      , Show (Thunk m)
      , Typeable (Thunk m)
      ) => MonadThunk m where
  type Thunk m :: *
  type ThunkValue m :: *
  thunk :: m (ThunkValue m) -> m (Thunk m)

  queryM :: Thunk m -> m r -> (ThunkValue m -> m r) -> m r
  force :: Thunk m -> (ThunkValue m -> m r) -> m r
  forceEff :: Thunk m -> (ThunkValue m -> m r) -> m r

  -- | Modify the action to be performed by the thunk. For some implicits
  --   this modifies the thunk, for others it may create a new thunk.
  further :: Thunk m -> (m (ThunkValue m) -> m (ThunkValue m)) -> m (Thunk m)

newtype ThunkLoop = ThunkLoop String -- contains rendering of ThunkId
  deriving Typeable

instance Show ThunkLoop where
  show (ThunkLoop i) = "ThunkLoop " ++ i

instance Exception ThunkLoop
