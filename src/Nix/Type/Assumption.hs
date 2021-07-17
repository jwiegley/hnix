-- | Basing on the Nix (Hindley–Milner) type system (that provides decidable type inference):
-- gathering assumptions (inference evidence) about polymorphic types.
{-# LANGUAGE TypeFamilies #-}
module Nix.Type.Assumption
  ( Assumption(..)
  , empty
  , lookup
  , remove
  , extend
  , keys
  , merge
  , mergeAssumptions
  , singleton
  )
where

import           Prelude                 hiding ( Type
                                                , empty
                                                )

import           Nix.Expr
import           Nix.Type.Type

newtype Assumption = Assumption { assumptions :: [(VarName, Type)] }
  deriving (Eq, Show)

-- We pretend that Assumptions can be inconsistent (nonunique keys),
-- (just like people in real life).
-- The consistency between assumptions is the inference responcibility.
instance Semigroup Assumption where
  (<>) = merge

instance Monoid Assumption where
  mempty = empty

instance One Assumption where
  type OneItem Assumption = (VarName, Type)
  one (x, y) = Assumption [(x, y)]

empty :: Assumption
empty = Assumption mempty

extend :: Assumption -> (VarName, Type) -> Assumption
extend (Assumption a) (x, s) =
  Assumption $
    (x, s) : a

remove :: Assumption -> VarName -> Assumption
remove (Assumption a) var =
  Assumption $
    filter
      (\(n, _) -> n /= var)
      a

lookup :: VarName -> Assumption -> [Type]
lookup key (Assumption a) =
  snd <$>
    filter
      (\(n, _) -> n == key)
      a

merge :: Assumption -> Assumption -> Assumption
merge (Assumption a) (Assumption b) =
  Assumption $ a <> b

mergeAssumptions :: [Assumption] -> Assumption
mergeAssumptions = foldl' (<>) mempty

singleton :: VarName -> Type -> Assumption
singleton x y = Assumption [(x, y)]

keys :: Assumption -> [VarName]
keys (Assumption a) = fst <$> a
