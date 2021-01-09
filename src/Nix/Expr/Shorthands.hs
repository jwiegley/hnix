{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | A bunch of shorthands for making nix expressions.
--
-- Functions with an @F@ suffix return a more general type without the outer
-- 'Fix' wrapper.
module Nix.Expr.Shorthands where

import           Data.Fix
import           Data.List.NonEmpty             ( NonEmpty(..) )
import           Data.Text                      ( Text )
import           Nix.Atoms
import           Nix.Utils
import           Nix.Expr.Types
import           Text.Megaparsec.Pos            ( SourcePos )

-- | Make an integer literal expression.
mkInt :: Integer -> NExpr
mkInt = Fix . mkIntF


mkIntF :: Integer -> NExprF a
mkIntF = NConstant . NInt

-- | Make an floating point literal expression.
mkFloat :: Float -> NExpr
mkFloat = Fix . mkFloatF

mkFloatF :: Float -> NExprF a
mkFloatF = NConstant . NFloat

-- | Make a regular (double-quoted) string.
mkStr :: Text -> NExpr
mkStr = Fix . NStr . DoubleQuoted . \case
  "" -> []
  x  -> [Plain x]

-- | Make an indented string.
mkIndentedStr :: Int -> Text -> NExpr
mkIndentedStr w = Fix . NStr . Indented w . \case
  "" -> []
  x  -> [Plain x]

-- | Make a path. Use 'True' if the path should be read from the
-- environment, else 'False'.
mkPath :: Bool -> FilePath -> NExpr
mkPath b = Fix . mkPathF b

mkPathF :: Bool -> FilePath -> NExprF a
mkPathF False = NLiteralPath
mkPathF True  = NEnvPath

-- | Make a path expression which pulls from the NIX_PATH env variable.
mkEnvPath :: FilePath -> NExpr
mkEnvPath = Fix . mkEnvPathF

mkEnvPathF :: FilePath -> NExprF a
mkEnvPathF = mkPathF True

-- | Make a path expression which references a relative path.
mkRelPath :: FilePath -> NExpr
mkRelPath = Fix . mkRelPathF

mkRelPathF :: FilePath -> NExprF a
mkRelPathF = mkPathF False

-- | Make a variable (symbol)
mkSym :: VarName -> NExpr
mkSym = Fix . mkSymF

mkSymF :: VarName -> NExprF a
mkSymF = NSym

mkSynHole :: VarName -> NExpr
mkSynHole = Fix . mkSynHoleF

mkSynHoleF :: VarName -> NExprF a
mkSynHoleF = NSynHole

mkSelector :: VarName -> NAttrPath NExpr
mkSelector = (:| []) . StaticKey

mkBool :: Bool -> NExpr
mkBool = Fix . mkBoolF

mkBoolF :: Bool -> NExprF a
mkBoolF = NConstant . NBool

mkNull :: NExpr
mkNull = Fix mkNullF

mkNullF :: NExprF a
mkNullF = NConstant NNull

mkOper :: NUnaryOp -> NExpr -> NExpr
mkOper op = Fix . NUnary op

mkOper2 :: NBinaryOp -> NExpr -> NExpr -> NExpr
mkOper2 op a = Fix . NBinary op a

mkParamset :: [(VarName, Maybe NExpr)] -> Bool -> Params NExpr
mkParamset params variadic = ParamSet params variadic Nothing

mkRecSet :: [Binding NExpr] -> NExpr
mkRecSet = Fix . NSet NRecursive

mkNonRecSet :: [Binding NExpr] -> NExpr
mkNonRecSet = Fix . NSet NNonRecursive

mkLets :: [Binding NExpr] -> NExpr -> NExpr
mkLets bindings = Fix . NLet bindings

mkList :: [NExpr] -> NExpr
mkList = Fix . NList

mkWith :: NExpr -> NExpr -> NExpr
mkWith e = Fix . NWith e

mkAssert :: NExpr -> NExpr -> NExpr
mkAssert e = Fix . NWith e

mkIf :: NExpr -> NExpr -> NExpr -> NExpr
mkIf e1 e2 = Fix . NIf e1 e2

mkFunction :: Params NExpr -> NExpr -> NExpr
mkFunction params = Fix . NAbs params

{-
mkDot :: NExpr -> VarName -> NExpr
mkDot e key = mkDots e [key]

-- | Create a dotted expression using only text.
mkDots :: NExpr -> [VarName] -> NExpr
mkDots e [] = e
mkDots (Fix (NSelect e keys' x)) keys =
  -- Special case: if the expression in the first argument is already
  -- a dotted expression, just extend it.
  Fix (NSelect e (keys' <> map (StaticKey ?? Nothing) keys) x)
mkDots e keys = Fix $ NSelect e (map (StaticKey ?? Nothing) keys) Nothing
-}

-- | An `inherit` clause without an expression to pull from.
inherit :: [NKeyName e] -> SourcePos -> Binding e
inherit = Inherit Nothing

-- | An `inherit` clause with an expression to pull from.
inheritFrom :: e -> [NKeyName e] -> SourcePos -> Binding e
inheritFrom expr = Inherit (Just expr)

-- | Shorthand for producing a binding of a name to an expression.
bindTo :: VarName -> NExpr -> Binding NExpr
bindTo name x = NamedVar (mkSelector name) x nullPos

-- | Infix version of bindTo.
($=) :: VarName -> NExpr -> Binding NExpr
($=) = bindTo

infixr 2 $=

-- | Append a list of bindings to a set or let expression.
-- For example, adding `[a = 1, b = 2]` to `let c = 3; in 4` produces
-- `let a = 1; b = 2; c = 3; in 4`.
appendBindings :: [Binding NExpr] -> NExpr -> NExpr
appendBindings newBindings (Fix e) = case e of
  NLet bindings e'    -> Fix $ NLet (bindings <> newBindings) e'
  NSet recur bindings -> Fix $ NSet recur (bindings <> newBindings)
  _                   -> error "Can only append bindings to a set or a let"

-- | Applies a transformation to the body of a nix function.
modifyFunctionBody :: (NExpr -> NExpr) -> NExpr -> NExpr
modifyFunctionBody f (Fix e) = case e of
  NAbs params body -> Fix $ NAbs params (f body)
  _                -> error "Not a function"

-- | A let statement with multiple assignments.
letsE :: [(VarName, NExpr)] -> NExpr -> NExpr
letsE pairs = Fix . NLet (map (uncurry bindTo) pairs)

-- | Wrapper for a single-variable @let@.
letE :: VarName -> NExpr -> NExpr -> NExpr
letE varName varExpr = letsE [(varName, varExpr)]

-- | Make an attribute set (non-recursive).
attrsE :: [(VarName, NExpr)] -> NExpr
attrsE pairs = Fix $ NSet NNonRecursive (map (uncurry bindTo) pairs)

-- | Make an attribute set (recursive).
recAttrsE :: [(VarName, NExpr)] -> NExpr
recAttrsE pairs = Fix $ NSet NRecursive (map (uncurry bindTo) pairs)

-- | Logical negation.
mkNot :: NExpr -> NExpr
mkNot = Fix . NUnary NNot

-- -- | Dot-reference into an attribute set.
-- (!.) :: NExpr -> VarName -> NExpr
-- (!.) = mkDot
-- infixl 8 !.

mkBinop :: NBinaryOp -> NExpr -> NExpr -> NExpr
mkBinop op e1 e2 = Fix (NBinary op e1 e2)

-- | Various nix binary operators
($==), ($!=), ($<), ($<=), ($>), ($>=), ($&&), ($||), ($->), ($//), ($+), ($-), ($*), ($/), ($++)
  :: NExpr -> NExpr -> NExpr
e1 $== e2 = mkBinop NEq e1 e2
e1 $!= e2 = mkBinop NNEq e1 e2
e1 $< e2 = mkBinop NLt e1 e2
e1 $<= e2 = mkBinop NLte e1 e2
e1 $> e2 = mkBinop NGt e1 e2
e1 $>= e2 = mkBinop NGte e1 e2
e1 $&& e2 = mkBinop NAnd e1 e2
e1 $|| e2 = mkBinop NOr e1 e2
e1 $-> e2 = mkBinop NImpl e1 e2
e1 $// e2 = mkBinop NUpdate e1 e2
e1 $+ e2 = mkBinop NPlus e1 e2
e1 $- e2 = mkBinop NMinus e1 e2
e1 $* e2 = mkBinop NMult e1 e2
e1 $/ e2 = mkBinop NDiv e1 e2
e1 $++ e2 = mkBinop NConcat e1 e2

-- | Function application expression.
(@@) :: NExpr -> NExpr -> NExpr
f @@ arg = mkBinop NApp f arg
infixl 1 @@

-- | Lambda shorthand.
(==>) :: Params NExpr -> NExpr -> NExpr
(==>) = mkFunction

infixr 1 ==>

(@.) :: NExpr -> VarName -> NExpr
obj @. name = Fix (NSelect obj (StaticKey name :| []) Nothing)
infixl 2 @.
