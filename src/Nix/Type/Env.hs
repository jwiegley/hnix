{-# LANGUAGE TypeFamilies #-}
module Nix.Type.Env
  ( Env(..)
  , empty
  , lookup
  , remove
  , extend
  , extends
  , merge
  , mergeEnvs
  , singleton
  , keys
  , fromList
  , toList
  )
where

import           Prelude                 hiding ( empty
                                                , toList
                                                , fromList
                                                )

import           Nix.Expr.Types
import           Nix.Type.Type

import qualified Data.Map                      as Map


-- * Typing Environment

newtype Env = TypeEnv (Map.Map VarName [Scheme])
  deriving (Eq, Show)

instance Semigroup Env where
  -- | Right-biased merge (override). Analogous to @//@ in @Nix@
  -- Since nature of environment is to update & grow.
  (<>) = mergeRight

instance Monoid Env where
  mempty = empty

instance One Env where
  type OneItem Env = (VarName, Scheme)
  one = uncurry singleton

empty :: Env
empty = TypeEnv mempty

extend :: Env -> (VarName, [Scheme]) -> Env
extend env (x, s) = TypeEnv $ Map.insert x s $ coerce env

remove :: Env -> VarName -> Env
remove (TypeEnv env) var = TypeEnv $ Map.delete var env

extends :: Env -> [(VarName, [Scheme])] -> Env
extends env xs = TypeEnv $ Map.fromList xs <> coerce env

lookup :: VarName -> Env -> Maybe [Scheme]
lookup key (TypeEnv tys) = Map.lookup key tys

merge :: Env -> Env -> Env
merge (TypeEnv a) (TypeEnv b) = TypeEnv $ a <> b

mergeRight :: Env -> Env -> Env
mergeRight (TypeEnv a) (TypeEnv b) = TypeEnv $ b <> a

mergeEnvs :: [Env] -> Env
mergeEnvs = foldl' (<>) mempty

singleton :: VarName -> Scheme -> Env
singleton x y = TypeEnv $ one (x, [y])

keys :: Env -> [VarName]
keys (TypeEnv env) = Map.keys env

fromList :: [(VarName, [Scheme])] -> Env
fromList xs = TypeEnv $ Map.fromList xs

toList :: Env -> [(VarName, [Scheme])]
toList (TypeEnv env) = Map.toList env

