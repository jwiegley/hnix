module Nix.Type.Type where

import qualified Data.HashMap.Lazy             as M
import           Data.Text                      ( Text )
import           Nix.Utils                      ( AttrSet, VarName )

-- | Hindrey-Milner type interface

newtype TVar = TV String
  deriving (Show, Eq, Ord)

data Type
  = TVar TVar                -- type variable
  | TCon String              -- known type
  | TSet Bool (AttrSet Type) -- heterogeneous map, bool if variadic
  | TList [Type]             -- heterogeneous list
  | (:~>) Type Type          -- type -> type
  | TMany [Type]             -- variant type
  deriving (Show, Eq, Ord)

data Scheme = Forall [TVar] Type -- forall a b. a -> b
  deriving (Show, Eq, Ord)

-- This models a set that unifies with any other set.
typeSet :: Type
typeSet = TSet True M.empty

typeList :: Type
typeList = TList []

infixr 1 :~>

typeFun :: [Type] -> Type
typeFun = foldr1 (:~>)

typeInt, typeFloat, typeBool, typeString, typePath, typeNull :: Type
typeInt = TCon "integer"
typeFloat = TCon "float"
typeBool = TCon "boolean"
typeString = TCon "string"
typePath = TCon "path"
typeNull = TCon "null"

type Name = VarName
