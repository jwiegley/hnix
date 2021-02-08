{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Nix.Thunk.Separate (NThunkF(..), MonadSeparateThunk, runSeparateThunkT, askThunkCache) where

import Control.Exception hiding (catch)
import Control.Monad.Catch
import Control.Monad.Reader
import Control.Monad.Ref
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Nix.Thunk

-- | The type of very basic thunks
data NThunkF m v
    = Value v
    | Thunk (ThunkId m) (SeparateThunkT v m v)

instance (Eq v, Eq (ThunkId m)) => Eq (NThunkF m v) where
    Value x == Value y = x == y
    Thunk x _ == Thunk y _ = x == y
    _ == _ = False              -- jww (2019-03-16): not accurate...

instance Show v => Show (NThunkF m v) where
    show (Value v) = show v
    show (Thunk _ _) = "<thunk>"

type MonadSeparateThunk m = (MonadThunkId m, MonadAtomicRef m, Ord (ThunkId m)) --TODO: ThunkId allocation also needs to be sufficiently deterministic

type ThunkCache m v = Ref m (Map (ThunkId m) (Maybe v))

--TODO: HashMap?
newtype SeparateThunkT v m a = SeparateThunkT (ReaderT (ThunkCache m v) m a)
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadRef
    , MonadAtomicRef
    , MonadCatch
    , MonadThrow
    )

askThunkCache :: Monad m => SeparateThunkT v m (ThunkCache m v)
askThunkCache = SeparateThunkT ask

runSeparateThunkT :: ThunkCache m v -> SeparateThunkT v m a -> m a
runSeparateThunkT c (SeparateThunkT a) = runReaderT a c

instance MonadTrans (SeparateThunkT v) where
    lift = SeparateThunkT . lift

instance MonadThunkId m => MonadThunkId (SeparateThunkT v m) where
    type ThunkId (SeparateThunkT v m) = ThunkId m

instance (MonadSeparateThunk m, MonadCatch m)
  => MonadThunk (NThunkF m v) (SeparateThunkT v m) v where
    thunk     = buildThunk
    thunkId   = \case
        Value _   -> Nothing
        Thunk n _ -> Just n
    query     = queryValue
    queryM    = queryThunk
    force     = forceThunk
    forceEff  = forceEffects
    wrapValue = valueRef
    getValue  = thunkValue

valueRef :: v -> NThunkF m v
valueRef = Value

thunkValue :: NThunkF m v -> Maybe v
thunkValue (Value v) = Just v
thunkValue _ = Nothing

buildThunk :: MonadThunkId m => SeparateThunkT v m v -> SeparateThunkT v m (NThunkF m v)
buildThunk action = do
    freshThunkId <- lift freshId
    return $ Thunk freshThunkId action

queryValue :: NThunkF m v -> a -> (v -> a) -> a
queryValue (Value v) _ k = k v
queryValue _ n _ = n

queryThunk :: (MonadAtomicRef m, Ord (ThunkId m)) => NThunkF m v -> SeparateThunkT v m a -> (v -> SeparateThunkT v m a) -> SeparateThunkT v m a
queryThunk (Value v) _ k = k v
queryThunk (Thunk tid _) n k = do
    c <- SeparateThunkT ask
    mOldVal <- atomicModifyRef' c $ \old ->
        -- Try to insert Nothing into the given key, but if something is already
        -- there, just leave it
        let (mOldVal, !new) = Map.insertLookupWithKey (\_ _ oldVal -> oldVal) tid Nothing old
        in (new, mOldVal)
    case mOldVal of
        Nothing -> do
            result <- n -- Not computed, inactive
            -- This is the only case where we've actually changed c, so restore it
            atomicModifyRef' c $ \old -> (Map.delete tid old, ())
            return result
        Just Nothing -> n -- Active
        Just (Just v) -> k v -- Computed, inactive

forceThunk
    :: forall m v a.
    ( MonadAtomicRef m
    , MonadThrow m
    , MonadCatch m
    , Show (ThunkId m)
    , Ord (ThunkId m)
    )
    => NThunkF m v -> (v -> SeparateThunkT v m a) -> SeparateThunkT v m a
forceThunk (Value v) k = k v
forceThunk (Thunk tid action) k = do
    c <- SeparateThunkT ask
    mOldVal <- atomicModifyRef' c $ \old ->
        -- Try to insert Nothing into the given key, but if something is already
        -- there, just leave it
        let (mOldVal, !new) = Map.insertLookupWithKey (\_ _ oldVal -> oldVal) tid Nothing old
        in (new, mOldVal)
    case mOldVal of
        Nothing -> do -- Not computed, inactive
            v <- catch action $ \(e :: SomeException) -> do
                -- This is the only case where we've actually changed c, so restore it
                _ <- atomicModifyRef' c $ \old -> (Map.delete tid old, ())
                throwM e
            atomicModifyRef' c $ \old -> (Map.insert tid (Just v) old, ())
            k v
        Just Nothing -> throwM $ ThunkLoop $ show tid
        Just (Just v) -> k v -- Computed, inactive

forceEffects :: (MonadAtomicRef m, Ord (ThunkId m)) => NThunkF m v -> (v -> SeparateThunkT v m r) -> SeparateThunkT v m r
forceEffects (Value v) k = k v
forceEffects (Thunk tid action) k = do
    c <- SeparateThunkT ask
    mOldVal <- atomicModifyRef' c $ \old ->
        -- Try to insert Nothing into the given key, but if something is already
        -- there, just leave it
        let (mOldVal, !new) = Map.insertLookupWithKey (\_ _ oldVal -> oldVal) tid Nothing old
        in (new, mOldVal)
    case mOldVal of
        Nothing -> do -- Not computed, inactive
            v <- action
            atomicModifyRef' c $ \old -> (Map.insert tid (Just v) old, ())
            k v
        Just Nothing -> return $ error "Loop detected"
        Just (Just v) -> k v -- Computed, inactive
