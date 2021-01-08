{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Nix.Fresh where

import           Control.Applicative
import           Control.Monad.Base
import           Control.Monad.Catch
import           Control.Monad.Except
#if !MIN_VERSION_base(4,13,0)
import           Control.Monad.Fail
#endif
import           Control.Monad.Reader
import           Control.Monad.Ref
import           Control.Monad.ST

import           Nix.Var

newtype FreshIdT i m a = FreshIdT { unFreshIdT :: ReaderT (Var m i) m a }
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadFail
    , MonadPlus
    , MonadFix
    , MonadRef
    , MonadAtomicRef
    , MonadIO
    , MonadCatch
    , MonadThrow
    , MonadMask
    )

instance MonadTrans (FreshIdT i) where
  lift = FreshIdT . lift

instance MonadBase b m => MonadBase b (FreshIdT i m) where
  liftBase = FreshIdT . liftBase

freshId :: (Monad m, MonadAtomicRef m, Enum i) => FreshIdT i m i
freshId = FreshIdT $ do
  v <- ask
  atomicModifyVar v (\i -> (succ i, i))

runFreshIdT :: Functor m => Var m i -> FreshIdT i m a -> m a
runFreshIdT i m = runReaderT (unFreshIdT m) i

-- Orphan instance needed by Infer.hs and Lint.hs

-- Since there's no forking, it's automatically atomic.
instance MonadAtomicRef (ST s) where
  atomicModifyRef r f = do
    v <- readRef r
    let (a, b) = f v
    writeRef r a
    return b
  atomicModifyRef' r f = do
    v <- readRef r
    let (a, b) = f v
    writeRef r $! a
    return b
