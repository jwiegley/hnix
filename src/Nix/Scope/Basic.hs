{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Nix.Scope.Basic where

import Control.Applicative
import Control.Monad.Exception
import Control.Monad.Fail
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Catch
import Nix.Thunk
import Nix.Scope
#ifdef MIN_VERSION_haskeline
import           System.Console.Haskeline.MonadException hiding(catch)
#endif

-- `binding` is the information associated with a variable name in the scope
newtype ScopeT binding r m a = ScopeT { unScopeT :: ReaderT (Scopes r binding) m a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , Alternative
    , MonadPlus
    , MonadFail
    , MonadFix
    , MonadIO
    , MonadCatch
    , MonadThrow
    , MonadException
    , MonadMask
    )

deriving instance MonadState s m => MonadState s (ScopeT binding r m)

instance MonadReader a m => MonadReader a (ScopeT binding r m) where
  ask = lift ask
  local f = liftWrap $ local f
  reader = lift . reader

runScopeT :: ScopeT binding r m a -> Scopes r binding -> m a
runScopeT = runReaderT . unScopeT

instance MonadTrans (ScopeT t r) where
  lift = ScopeT . lift

instance (Monad m, Monad r) => Scoped r t (ScopeT t r m) where
  currentScopes = ScopeT ask
  clearScopes = ScopeT . local (const mempty) . unScopeT
  pushScopes added = 
    ScopeT .
    local (\old -> added <> old) .
    unScopeT
  askLookupVar name = ScopeT $ do
    scopes <- ask
    pure $ lookupVarScopes name scopes

instance MonadThunk m => MonadThunk (ScopeT binding r m) where
  type Thunk (ScopeT binding r m) = Thunk m
  type ThunkValue (ScopeT binding r m) = ThunkValue m
  thunk a = ScopeT $ do
    scopes <- ask
    lift $ thunk $ runScopeT a scopes
  queryM t n k = ScopeT $ do
    scopes <- ask
    lift $ queryM t (runScopeT n scopes) ((`runScopeT` scopes) . k)
  force t k = ScopeT $ do
    scopes <- ask
    lift $ force t $ (`runScopeT` scopes) . k
  forceEff t k = ScopeT $ do
    scopes <- ask
    lift $ forceEff t $ (`runScopeT` scopes) . k
  further t k = ScopeT $ do
    scopes <- ask
    lift $ further t $ (`runScopeT` scopes) . k . lift

instance MonadTransWrap (ScopeT binding r) where
  liftWrap f a = ScopeT $ liftWrap f (unScopeT a)
