
-- | A bunch of shorthands for making nix expressions.
--
-- Functions with an @F@ suffix return a more general type (base functor @F a@) without the outer
-- 'Fix' wrapper that creates @a@.
module Nix.Expr.Shorthands where

import           Data.Fix
import           Nix.Atoms
import           Nix.Expr.Types
import           Nix.Utils

-- * Basic expression builders

-- | Put @NAtom@ as expression
mkConst :: NAtom -> NExpr
mkConst = Fix . NConstant

-- | Put null.
mkNull :: NExpr
mkNull = Fix mkNullF

-- | Put boolean.
mkBool :: Bool -> NExpr
mkBool = Fix . mkBoolF

-- | Put integer.
mkInt :: Integer -> NExpr
mkInt = Fix . mkIntF

-- | Put floating point number.
mkFloat :: Float -> NExpr
mkFloat = Fix . mkFloatF

-- | Put a regular (double-quoted) string.
mkStr :: Text -> NExpr
mkStr = Fix . NStr . DoubleQuoted .
  whenText
    mempty
    (one . Plain)

-- | Put an indented string.
mkIndentedStr :: Int -> Text -> NExpr
mkIndentedStr w = Fix . NStr . Indented w .
  whenText
    mempty
    (one . Plain)

-- | Put a path. Use @True@ if the path should be read from the environment, else use @False@.
mkPath :: Bool -> FilePath -> NExpr
mkPath b = Fix . mkPathF b

-- | Put a path expression which pulls from the @NIX_PATH@ @env@ variable.
mkEnvPath :: FilePath -> NExpr
mkEnvPath = Fix . mkEnvPathF

-- | Put a path which references a relative path.
mkRelPath :: FilePath -> NExpr
mkRelPath = Fix . mkRelPathF

-- | Put a variable (symbol).
mkSym :: Text -> NExpr
mkSym = Fix . mkSymF

-- | Put syntactic hole.
mkSynHole :: Text -> NExpr
mkSynHole = Fix . mkSynHoleF

mkSelector :: Text -> NAttrPath NExpr
mkSelector = (:| mempty) . StaticKey . coerce

-- | Put an unary operator.
mkOp :: NUnaryOp -> NExpr -> NExpr
mkOp op = Fix . NUnary op

-- | Logical negation: @not@.
mkNot :: NExpr -> NExpr
mkNot = mkOp NNot

-- | Number negation: @-@.
--
-- Negation in the language works with integers and floating point.
mkNeg :: NExpr -> NExpr
mkNeg = mkOp NNeg

-- | Put a binary operator.
mkOp2 :: NBinaryOp -> NExpr -> NExpr -> NExpr
mkOp2 op a = Fix . NBinary op a

mkParamset :: [(Text, Maybe NExpr)] -> Bool -> Params NExpr
mkParamset params variadic = ParamSet (coerce params) variadic Nothing

-- | Put a recursive set.
--
-- @rec { .. };@
mkRecSet :: [Binding NExpr] -> NExpr
mkRecSet = mkSet Recursive

-- | Put a non-recursive set.
--
-- > { .. }
mkNonRecSet :: [Binding NExpr] -> NExpr
mkNonRecSet = mkSet NonRecursive

-- | General set builder function.
mkSet :: Recursivity -> [Binding NExpr] -> NExpr
mkSet r = Fix . NSet r

-- | Empty set.
--
-- Monoid. Use @//@ operation (shorthand $//) to extend the set.
emptySet :: NExpr
emptySet = mkNonRecSet mempty

-- | Put a list.
mkList :: [NExpr] -> NExpr
mkList = Fix . NList

emptyList :: NExpr
emptyList = mkList mempty

-- | Wrap in a @let@.
--
-- (Evaluate the second argument after introducing the bindings.)
--
-- +------------------------+-----------------+
-- | Haskell                | Nix             |
-- +========================+=================+
-- | @mkLets bindings expr@ | @let bindings;@ |
-- |                        | @in expr@       |
-- +------------------------+-----------------+
mkLets :: [Binding NExpr] -> NExpr -> NExpr
mkLets bindings = Fix . NLet bindings

-- | Create a @whith@:
-- 1st expr - what to bring into the scope.
-- 2nd - expression that recieves the scope extention.
--
-- +--------------------+-------------------+
-- | Haskell            | Nix               |
-- +====================+===================+
-- | @mkWith body main@ | @with body; expr@ |
-- +--------------------+-------------------+
mkWith :: NExpr -> NExpr -> NExpr
mkWith e = Fix . NWith e

-- | Create an @assert@:
-- 1st expr - asserting itself, must return @true@.
-- 2nd - main expression to evaluated after assertion.
--
-- +-----------------------+----------------------+
-- | Haskell               | Nix                  |
-- +=======================+======================+
-- | @mkAssert check eval@ | @assert check; eval@ |
-- +-----------------------+----------------------+
mkAssert :: NExpr -> NExpr -> NExpr
mkAssert e = Fix . NAssert e

-- | Put:
--
-- > if expr1
-- >   then expr2
-- >   else expr3
mkIf :: NExpr -> NExpr -> NExpr -> NExpr
mkIf e1 e2 = Fix . NIf e1 e2

-- | Lambda function, analog of Haskell's @\\ x -> x@:
--
-- +-----------------------+-----------+
-- | Haskell               | Nix       |
-- +=======================+===========+
-- | @ mkFunction x expr @ | @x: expr@ |
-- +-----------------------+-----------+
mkFunction :: Params NExpr -> NExpr -> NExpr
mkFunction params = Fix . NAbs params

-- | General dot-reference with optional alternative if the jey does not exist.
getRefOrDefault :: Maybe NExpr -> NExpr -> Text -> NExpr
getRefOrDefault alt obj name = Fix $ NSelect alt obj (mkSelector name)

-- ** Base functor builders for basic expressions builders *sic

-- | Unfixed @mkNull@.
mkNullF :: NExprF a
mkNullF = NConstant NNull

-- | Unfixed @mkBool@.
mkBoolF :: Bool -> NExprF a
mkBoolF = NConstant . NBool

-- | Unfixed @mkInt@.
mkIntF :: Integer -> NExprF a
mkIntF = NConstant . NInt

-- | Unfixed @mkFloat@.
mkFloatF :: Float -> NExprF a
mkFloatF = NConstant . NFloat

-- | Unfixed @mkPath@.
mkPathF :: Bool -> FilePath -> NExprF a
mkPathF False = NLiteralPath
mkPathF True  = NEnvPath

-- | Unfixed @mkEnvPath@.
mkEnvPathF :: FilePath -> NExprF a
mkEnvPathF = mkPathF True

-- | Unfixed @mkRelPath@.
mkRelPathF :: FilePath -> NExprF a
mkRelPathF = mkPathF False

-- | Unfixed @mkSym@.
mkSymF :: Text -> NExprF a
mkSymF = NSym . coerce

-- | Unfixed @mkSynHole@.
mkSynHoleF :: Text -> NExprF a
mkSynHoleF = NSynHole . coerce


-- * Other
-- (org this better/make a better name for section(s))

-- | An `inherit` clause with an expression to pull from.
--
-- +------------------------+--------------------+------------+
-- | Hask                   | Nix                | pseudocode |
-- +========================+====================+============+
-- | @inheritFrom x [a, b]@ | @inherit (x) a b;@ | @a = x.a;@ |
-- |                        |                    | @b = x.b;@ |
-- +------------------------+--------------------+------------+
inheritFrom :: e -> [NKeyName e] -> Binding e
inheritFrom expr ks = Inherit (pure expr) ks nullPos

-- | An `inherit` clause without an expression to pull from.
--
-- +----------------------+----------------+------------------+
-- | Hask                 | Nix            | pseudocode       |
-- +======================+================+==================+
-- | @inheritFrom [a, b]@ | @inherit a b;@ | @a = outside.a;@ |
-- |                      |                | @b = outside.b;@ |
-- +----------------------+----------------+------------------+
inherit :: [NKeyName e] -> Binding e
inherit ks = Inherit Nothing ks nullPos

-- | Nix @=@ (bind operator).
($=) :: Text -> NExpr -> Binding NExpr
($=) = bindTo
infixr 2 $=

-- | Shorthand for producing a binding of a name to an expression: Nix's @=@.
bindTo :: Text -> NExpr -> Binding NExpr
bindTo name x = NamedVar (mkSelector name) x nullPos

-- | Append a list of bindings to a set or let expression.
-- For example:
-- adding      `[a = 1, b = 2]`
-- to       `let               c = 3; in 4`
-- produces `let a = 1; b = 2; c = 3; in 4`.
appendBindings :: [Binding NExpr] -> NExpr -> NExpr
appendBindings newBindings (Fix e) =
  case e of
    NLet bindings e'    -> mkLets (bindings <> newBindings) e'
    NSet recur bindings -> Fix $ NSet recur (bindings <> newBindings)
    _                   -> error "Can only append bindings to a set or a let"

-- | Applies a transformation to the body of a Nix function.
modifyFunctionBody :: (NExpr -> NExpr) -> NExpr -> NExpr
modifyFunctionBody transform (Fix (NAbs params body)) = mkFunction params $ transform body
modifyFunctionBody _ _ = error "Not a function"

-- | A @let@ statement with multiple assignments.
letsE :: [(Text, NExpr)] -> NExpr -> NExpr
letsE pairs = mkLets $ uncurry ($=) <$> pairs

-- | Wrapper for a single-variable @let@.
letE :: Text -> NExpr -> NExpr -> NExpr
letE varName varExpr = letsE [(varName, varExpr)]

-- | Make a non-recursive attribute set.
attrsE :: [(Text, NExpr)] -> NExpr
attrsE pairs = mkNonRecSet $ uncurry ($=) <$> pairs

-- | Make a recursive attribute set.
recAttrsE :: [(Text, NExpr)] -> NExpr
recAttrsE pairs = mkRecSet $ uncurry ($=) <$> pairs


-- * Nix binary operators

(@@), ($==), ($!=), ($<), ($<=), ($>), ($>=), ($&&), ($||), ($->), ($//), ($+), ($-), ($*), ($/), ($++)
  :: NExpr -> NExpr -> NExpr
--  2021-07-10: NOTE: Probably the presedence of some operators is still needs to be tweaked.

-- | Dot-reference into an attribute set: @attrSet.k@
(@.) :: NExpr -> Text -> NExpr
(@.) = getRefOrDefault Nothing
infix 9 @.

-- | Dot-reference into an attribute set with alternative if the key does not exist.
--
-- > s.x or y
(@.<|>) :: NExpr -> Text -> NExpr -> NExpr
(@.<|>) obj name alt = getRefOrDefault (pure alt ) obj name
infix 9 @.<|>

-- | Function application (@' '@ in @f x@)
(@@) = mkOp2 NApp
infixl 8 @@

-- | List concatenation: @++@
($++) = mkOp2 NConcat
infixr 7 $++

-- | Multiplication: @*@
($*)  = mkOp2 NMult
infixl 6 $*

-- | Division: @/@
($/)  = mkOp2 NDiv
infixl 6 $/

-- | Addition: @+@
($+)  = mkOp2 NPlus
infixl 5 $+

-- | Subtraction: @-@
($-)  = mkOp2 NMinus
infixl 5 $-

-- | Extend/override the left attr set, with the right one: @//@
($//) = mkOp2 NUpdate
infixr 5 $//

-- | Greater than: @>@
($>)  = mkOp2 NGt
infix 4 $>

-- | Greater than OR equal: @>=@
infix 4 $>=
($>=) = mkOp2 NGte

-- | Less than OR equal: @<=@
($<=) = mkOp2 NLte
infix 4 $<=

-- | Less than: @<@
($<)  = mkOp2 NLt
infix 4 $<

-- | Equality: @==@
($==) = mkOp2 NEq
infix 3 $==

-- | Inequality: @!=@
($!=) = mkOp2 NNEq
infix 3 $!=

-- | AND: @&&@
($&&) = mkOp2 NAnd
infixl 2 $&&

-- | OR: @||@
($||) = mkOp2 NOr
infixl 2 $||

-- | Logical implication: @->@
($->) = mkOp2 NImpl
infix 1 $->

-- | Lambda function, analog of Haskell's @\\ x -> x@:
--
-- +---------------+-----------+
-- | Haskell       | Nix       |
-- +===============+===========+
-- | @x ==> expr @ | @x: expr@ |
-- +---------------+-----------+
(==>) :: Params NExpr -> NExpr -> NExpr
(==>) = mkFunction
infixr 1 ==>


-- * Under deprecation

-- NOTE: Remove after 2023-07
-- | Put an unary operator.
mkOper :: NUnaryOp -> NExpr -> NExpr
mkOper op = Fix . NUnary op

-- NOTE: Remove after 2023-07
-- | Put a binary operator.
mkOper2 :: NBinaryOp -> NExpr -> NExpr -> NExpr
mkOper2 op a = Fix . NBinary op a

-- NOTE: Remove after 2023-07
-- | Nix binary operator builder.
mkBinop :: NBinaryOp -> NExpr -> NExpr -> NExpr
mkBinop = mkOp2
