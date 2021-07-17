-- | The basis of the Nix type system (type-level).
--   Based on the Hindley–Milner type system.
--   Therefore -> from this the type inference follows.
module Nix.Type.Type where

import           Prelude                 hiding ( Type, TVar )
import           Data.Foldable                  ( foldr1 )
import           Nix.Expr.Types                 ( AttrSet )

-- | Hindrey-Milner type interface

-- | Type variable in the Nix type system.
newtype TVar = TV Text
  deriving (Show, Eq, Ord)

-- | The basic type definitions in the Nix type system (type-level code).
data Type
  = TVar TVar                -- ^ Type variable in the Nix type system.
  | TCon Text                -- ^ Concrete (non-polymorphic, constant) type in the Nix type system.
  | TSet Bool (AttrSet Type) -- ^ Heterogeneous map in the Nix type system. @True@ -> variadic.
  | TList [Type]             -- ^ Heterogeneous list in the Nix type system.
  | (:~>) Type Type          -- ^ Type arrow (@Type -> Type@) in the Nix type system.
  | TMany [Type]             -- ^ Variant type (term). Since relating to Nix type system, more precicely -
                             --   dynamic types in dynamicly typed language (which is Nix).
  deriving (Show, Eq, Ord)

infixr 1 :~>

-- | Hindley–Milner type system uses "scheme" term for "polytypes".
--   Types containing @forall@ quantifiers: @forall a . a@.
--   Note: HM allows only top-level @forall@ quantification, so no @RankNTypes@ in it.
data Scheme = Forall [TVar] Type -- ^ @Forall [TVar] Type@: the Nix type system @forall vars. type@.
  deriving (Show, Eq, Ord)

-- This models a set that unifies with any other set.
typeSet :: Type
typeSet = TSet True mempty

typeList :: Type
typeList = TList mempty

typeFun :: [Type] -> Type
-- Please, replace with safe analog to `foldr1`
typeFun = foldr1 (:~>)

-- | Concrete types in the Nix type system.
typeInt, typeFloat, typeBool, typeString, typePath, typeNull :: Type
typeInt    = TCon "integer"
typeFloat  = TCon "float"
typeBool   = TCon "boolean"
typeString = TCon "string"
typePath   = TCon "path"
typeNull   = TCon "null"
