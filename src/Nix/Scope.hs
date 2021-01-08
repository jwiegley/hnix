{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Nix.Scope where

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.Trans.Writer
import qualified Data.HashMap.Lazy             as M
import           Data.Text                      ( Text )
import           Lens.Family2
import           Nix.Utils

class Scoped r binding m | m -> binding r where
  currentScopes :: m (Scopes r binding)
  clearScopes :: m x -> m x
  pushScopes :: Scopes r binding -> m x -> m x
  askLookupVar :: Text -> m (r (Maybe binding))

lookupVar :: (Monad m, Scoped m binding m) => Text -> m (Maybe binding)
lookupVar = join . askLookupVar

newtype Scope a = Scope { getScope :: AttrSet a }
    deriving (Functor, Foldable, Traversable, Eq)

instance Show (Scope a) where
  show (Scope m) = show (M.keys m)

newScope :: AttrSet a -> Scope a
newScope = Scope

scopeLookup :: Text -> [Scope a] -> Maybe a
scopeLookup key = foldr go Nothing
  where go (Scope m) rest = M.lookup key m <|> rest

data Scopes m a = Scopes
    { lexicalScopes :: [Scope a]
    , dynamicScopes :: [m (Scope a)]
    }

instance Show (Scopes m a) where
  show (Scopes m a) =
    "Scopes: " ++ show m ++ ", and " ++ show (length a) ++ " with-scopes"

instance Semigroup (Scopes m a) where
  Scopes ls lw <> Scopes rs rw = Scopes (ls <> rs) (lw <> rw)

instance Monoid (Scopes m a) where
  mempty  = emptyScopes
  mappend = (<>)

instance Functor m => Functor (Scopes m) where
  fmap f (Scopes l d) = Scopes (fmap (fmap f) l) (fmap (fmap (fmap f)) d)

emptyScopes :: forall m a . Scopes m a
emptyScopes = Scopes [] []

currentScopesReader
  :: forall m a e . (MonadReader e m, Has e (Scopes m a)) => m (Scopes m a)
currentScopesReader = asks (view hasLens)

clearScopesReader
  :: forall m a e r . (MonadReader e m, Has e (Scopes m a)) => m r -> m r
clearScopesReader = local (set hasLens (emptyScopes @m @a))

strongScope :: AttrSet a -> Scopes m a
strongScope a = Scopes [Scope a] []

pushScope :: Scoped r a m => AttrSet a -> m x -> m x
pushScope s = pushScopes (Scopes [Scope s] [])

pushWeakScope :: (Functor r, Scoped r a m) => r (AttrSet a) -> m x -> m x
pushWeakScope s = pushScopes (Scopes [] [Scope <$> s])

pushScopesReader
  :: (MonadReader e m, Has e (Scopes r a)) => Scopes r a -> m x -> m x
pushScopesReader s = local (over hasLens (s <>))

lookupVarReader
  :: forall r m a e . (Monad r, MonadReader e m, Has e (Scopes r a)) => Text -> m (r (Maybe a))
lookupVarReader k = do
  s <- asks $ view hasLens
  pure $ lookupVarScopes k s

lookupVarScopes
  :: forall m a . Monad m => Text -> Scopes m a -> m (Maybe a)
lookupVarScopes k s = do
  let mres = scopeLookup k $ lexicalScopes @m s
  case mres of
    Just sym -> pure $ Just sym
    Nothing  -> do
      let ws = dynamicScopes s
      foldr
        (\x rest -> do
          mres' <- M.lookup k . getScope <$> x
          case mres' of
            Just sym -> pure $ Just sym
            Nothing  -> rest
        )
        (pure Nothing)
        ws

withScopes :: Scoped r a m => Scopes r a -> m x -> m x
withScopes scope = clearScopes . pushScopes scope

hoistDynamicScopes :: (m (Scope a) -> n (Scope a)) -> Scopes m a -> Scopes n a
hoistDynamicScopes f (Scopes s d) = Scopes s $ fmap f d

instance (Scoped r a m, Monoid w, Monad m) => Scoped r a (WriterT w m) where
  currentScopes = lift currentScopes
  clearScopes m = do
    (a, w) <- lift $ clearScopes $ runWriterT m
    tell w
    pure a
  pushScopes s m = do
    (a, w) <- lift $ pushScopes s $ runWriterT m
    tell w
    pure a
  askLookupVar = lift . askLookupVar
