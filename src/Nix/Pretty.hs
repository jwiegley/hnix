{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Nix.Pretty where

import           Control.Arrow                  ( first )
import           Control.Applicative            ( (<|>) )
import           Control.Monad.Free
import           Data.Fix                       ( Fix(..), foldFix )
import           Data.HashMap.Lazy              ( toList )
import qualified Data.HashMap.Lazy             as M
import qualified Data.HashSet                  as HashSet
import           Data.List                      ( isPrefixOf
                                                , sort
                                                )
import           Data.Interned                  ( intern, unintern )
import           Data.Interned.Text
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import           Data.Maybe                     ( isJust
                                                , fromMaybe
                                                )
import           Data.Text                      ( pack
                                                , unpack
                                                , replace
                                                , strip
                                                )
import qualified Data.Text                     as Text
import           Nix.Atoms
import           Nix.Cited
import           Nix.Expr
import           Nix.Expr.Strings
import           Nix.Normal
import           Nix.Parser
import           Nix.String
import           Nix.Thunk
import           Nix.Value
import           Prettyprinter
import           Text.Read                      ( readMaybe )

-- | This type represents a pretty printed nix expression
-- together with some information about the expression.
data NixDoc ann = NixDoc
  { -- | The rendered expression, without any parentheses.
    withoutParens    :: Doc ann

    -- | The root operator is the operator at the root of
    -- the expression tree. For example, in '(a * b) + c', '+' would be the root
    -- operator. It is needed to determine if we need to wrap the expression in
    -- parentheses.
  , rootOp :: OperatorInfo
  , wasPath :: Bool -- This is needed so that when a path is used in a selector path
                    -- we can add brackets appropriately
  }

mkNixDoc :: Doc ann -> OperatorInfo -> NixDoc ann
mkNixDoc d o = NixDoc { withoutParens = d, rootOp = o, wasPath = False }

-- | A simple expression is never wrapped in parentheses. The expression
--   behaves as if its root operator had a precedence higher than all
--   other operators (including function application).
simpleExpr :: Doc ann -> NixDoc ann
simpleExpr d = mkNixDoc d (OperatorInfo minBound NAssocNone "simple expr")

pathExpr :: Doc ann -> NixDoc ann
pathExpr d = (simpleExpr d) { wasPath = True }

-- | An expression that behaves as if its root operator had a precedence lower
--   than all other operators. That ensures that the expression is wrapped in
--   parentheses in almost always, but it's still rendered without parentheses
--   in cases where parentheses are never required (such as in the LHS of a
--   binding).
leastPrecedence :: Doc ann -> NixDoc ann
leastPrecedence =
  flip mkNixDoc $ OperatorInfo maxBound NAssocNone "least precedence"

appOp :: OperatorInfo
appOp = getBinaryOperator NApp

appOpNonAssoc :: OperatorInfo
appOpNonAssoc = (getBinaryOperator NApp) { associativity = NAssocNone }

selectOp :: OperatorInfo
selectOp = getSpecialOperator NSelectOp

hasAttrOp :: OperatorInfo
hasAttrOp = getSpecialOperator NHasAttrOp

wrapParens :: OperatorInfo -> NixDoc ann -> Doc ann
wrapParens op sub
  | precedence (rootOp sub) < precedence op
  = withoutParens sub
  | precedence (rootOp sub)
    == precedence op
    && associativity (rootOp sub)
    == associativity op
    && associativity op
    /= NAssocNone
  = withoutParens sub
  | otherwise
  = parens $ withoutParens sub

-- Used in the selector case to print a path in a selector as
-- "${./abc}"
wrapPath :: OperatorInfo -> NixDoc ann -> Doc ann
wrapPath op sub = if wasPath sub
  then dquotes $ "$" <> braces (withoutParens sub)
  else wrapParens op sub

prettyString :: NString (NixDoc ann) -> Doc ann
prettyString (DoubleQuoted parts) = dquotes . hcat . map prettyPart $ parts
 where
  prettyPart (Plain t)      = pretty . concatMap escape . unpack $ t
  prettyPart EscapedNewline = "''\\n"
  prettyPart (Antiquoted r) = "$" <> braces (withoutParens r)
  escape '"' = "\\\""
  escape x   = maybe [x] (('\\' :) . (: [])) $ toEscapeCode x
prettyString (Indented _ parts) = group $ nest 2 $ vcat
  [dsquote, content, dsquote]
 where
  dsquote = squote <> squote
  content = vsep . map prettyLine . stripLastIfEmpty . splitLines $ parts
  stripLastIfEmpty = reverse . f . reverse   where
    f ([Plain t] : xs) | Text.null (strip t) = xs
    f xs = xs
  prettyLine = hcat . map prettyPart
  prettyPart (Plain t) =
    pretty . unpack . replace "${" "''${" . replace "''" "'''" $ t
  prettyPart EscapedNewline = "\\n"
  prettyPart (Antiquoted r) = "$" <> braces (withoutParens r)

prettyParams :: Params (NixDoc ann) -> Doc ann
prettyParams (Param n           ) = pretty $ unpack $ unintern n
prettyParams (ParamSet s v mname) = prettyParamSet s v <> case mname of
  Nothing -> mempty
  Just name | Text.null (unintern name) -> mempty
            | otherwise      -> "@" <> pretty (unpack $ unintern name)

prettyParamSet :: ParamSet (NixDoc ann) -> Bool -> Doc ann
prettyParamSet args var = encloseSep
  (lbrace <> space)
  (align (space <> rbrace))
  sep
  (map prettySetArg args ++ prettyVariadic)
 where
  prettySetArg (n, maybeDef) = case maybeDef of
    Nothing -> pretty (unpack $ unintern n)
    Just v  -> pretty (unpack $ unintern n) <+> "?" <+> withoutParens v
  prettyVariadic = [ "..." | var ]
  sep            = align (comma <> space)

prettyBind :: Binding (NixDoc ann) -> Doc ann
prettyBind (NamedVar n v _p) =
  prettySelector n <+> equals <+> withoutParens v <> semi
prettyBind (Inherit s ns _p) =
  "inherit" <+> scope <> align (fillSep (map prettyKeyName ns)) <> semi
  where scope = maybe mempty ((<> space) . parens . withoutParens) s

prettyKeyName :: NKeyName (NixDoc ann) -> Doc ann
prettyKeyName (StaticKey "") = dquotes ""
prettyKeyName (StaticKey key) | HashSet.member (unintern key) reservedNames =
  dquotes $ pretty $ unpack $ unintern key
prettyKeyName (StaticKey  key) = pretty . unpack . unintern $ key
prettyKeyName (DynamicKey key) = runAntiquoted
  (DoubleQuoted [Plain "\n"])
  prettyString
  (("$" <>) . braces . withoutParens)
  key

prettySelector :: NAttrPath (NixDoc ann) -> Doc ann
prettySelector = hcat . punctuate dot . map prettyKeyName . NE.toList

prettyAtom :: NAtom -> NixDoc ann
prettyAtom atom = simpleExpr $ pretty $ unpack $ atomText atom

prettyNix :: NExpr -> Doc ann
prettyNix = withoutParens . foldFix exprFNixDoc

instance HasCitations1 m v f
  => HasCitations m v (NValue' t f m a) where
  citations (NValue f) = citations1 f
  addProvenance x (NValue f) = NValue (addProvenance1 x f)

instance (HasCitations1 m v f, HasCitations m v t)
  => HasCitations m v (NValue t f m) where
  citations (Pure t) = citations t
  citations (Free v) = citations v
  addProvenance x (Pure t) = Pure (addProvenance x t)
  addProvenance x (Free v) = Free (addProvenance x v)

prettyOriginExpr
  :: forall t f m ann
   . HasCitations1 m (NValue t f m) f
  => NExprLocF (Maybe (NValue t f m))
  -> Doc ann
prettyOriginExpr = withoutParens . go
 where
  go = exprFNixDoc . annotated . getCompose . fmap render

  render :: Maybe (NValue t f m) -> NixDoc ann
  render Nothing = simpleExpr "_"
  render (Just (Free (reverse . citations @m -> p:_))) = go (_originExpr p)
  render _       = simpleExpr "?"
    -- render (Just (NValue (citations -> ps))) =
        -- simpleExpr $ foldr ((\x y -> vsep [x, y]) . parens . indent 2 . withoutParens
        --                           . go . originExpr)
        --     mempty (reverse ps)

exprFNixDoc :: NExprF (NixDoc ann) -> NixDoc ann
exprFNixDoc = \case
  NConstant atom -> prettyAtom atom
  NStr      str  -> simpleExpr $ prettyString str
  NList     []   -> simpleExpr $ lbracket <> rbracket
  NList xs ->
    simpleExpr
      $ group
      $ nest 2
      $ vsep
      $ concat
      $ [[lbracket], map (wrapParens appOpNonAssoc) xs, [rbracket]]
  NSet NNonRecursive [] -> simpleExpr $ lbrace <> rbrace
  NSet NNonRecursive xs ->
    simpleExpr
      $ group
      $ nest 2
      $ vsep
      $ concat
      $ [[lbrace], map prettyBind xs, [rbrace]]
  NSet NRecursive [] -> simpleExpr $ recPrefix <> lbrace <> rbrace
  NSet NRecursive xs ->
    simpleExpr
      $ group
      $ nest 2
      $ vsep
      $ concat
      $ [[recPrefix <> lbrace], map prettyBind xs, [rbrace]]
  NAbs args body ->
    leastPrecedence
      $ nest 2
      $ vsep
      $ [prettyParams args <> colon, withoutParens body]
  NBinary NApp fun arg ->
    mkNixDoc (wrapParens appOp fun <+> wrapParens appOpNonAssoc arg) appOp
  NBinary op r1 r2 -> flip mkNixDoc opInfo $ hsep
    [ wrapParens (f NAssocLeft) r1
    , pretty $ unpack $ operatorName opInfo
    , wrapParens (f NAssocRight) r2
    ]
   where
    opInfo = getBinaryOperator op
    f x | associativity opInfo /= x = opInfo { associativity = NAssocNone }
        | otherwise                 = opInfo
  NUnary op r1 -> mkNixDoc
    (pretty (unpack (operatorName opInfo)) <> wrapParens opInfo r1)
    opInfo
    where opInfo = getUnaryOperator op
  NSelect r' attr o ->
    (if isJust o then leastPrecedence else flip mkNixDoc selectOp)
      $  wrapPath selectOp r
      <> dot
      <> prettySelector attr
      <> ordoc
   where
    r     = flip mkNixDoc selectOp $ wrapParens appOpNonAssoc r'
    ordoc = maybe mempty (((space <> "or") <+>) . wrapParens appOpNonAssoc) o
  NHasAttr r attr ->
    mkNixDoc (wrapParens hasAttrOp r <+> "?" <+> prettySelector attr) hasAttrOp
  NEnvPath     p -> simpleExpr $ pretty ("<" ++ p ++ ">")
  NLiteralPath p -> pathExpr $ pretty $ case p of
    "./"  -> "./."
    "../" -> "../."
    ".."  -> "../."
    txt | "/" `isPrefixOf` txt   -> txt
        | "~/" `isPrefixOf` txt  -> txt
        | "./" `isPrefixOf` txt  -> txt
        | "../" `isPrefixOf` txt -> txt
        | otherwise              -> "./" ++ txt
  NSym name -> simpleExpr $ pretty (unpack $ unintern name)
  NLet binds body ->
    leastPrecedence
      $ group
      $ vsep
      $ [ "let"
        , indent 2 (vsep (map prettyBind binds))
        , "in" <+> withoutParens body
        ]
  NIf cond trueBody falseBody ->
    leastPrecedence
      $ group
      $ nest 2
      $ vsep
      $ [ "if" <+> withoutParens cond
        , align ("then" <+> withoutParens trueBody)
        , align ("else" <+> withoutParens falseBody)
        ]
  NWith scope body ->
    leastPrecedence
      $ vsep
      $ ["with" <+> withoutParens scope <> semi, align $ withoutParens body]
  NAssert cond body ->
    leastPrecedence
      $ vsep
      $ ["assert" <+> withoutParens cond <> semi, align $ withoutParens body]
  NSynHole name -> simpleExpr $ pretty ("^" <> unpack (unintern name))
  where recPrefix = "rec" <> space

valueToExpr :: forall t f m . MonadDataContext f m => NValue t f m -> NExpr
valueToExpr = iterNValue (\_ _ -> thk) phi
 where
  thk = Fix . NSym . intern . pack $ "<CYCLE>"

  phi :: NValue' t f m NExpr -> NExpr
  phi (NVConstant' a ) = Fix $ NConstant a
  phi (NVStr'      ns) = mkStr ns
  phi (NVList'     l ) = Fix $ NList l
  phi (NVSet' s p    ) = Fix $ NSet NNonRecursive
    [ NamedVar (StaticKey k :| []) v (fromMaybe nullPos (M.lookup k p))
    | (k, v) <- toList s
    ]
  phi (NVClosure' _ _   ) = Fix . NSym . intern . pack $ "<closure>"
  phi (NVPath' p        ) = Fix $ NLiteralPath p
  phi (NVBuiltin' name _) = Fix . NSym . intern . pack $ "builtins." ++ (Text.unpack $unintern name)
  phi _                   = error "Pattern synonyms foil completeness check"

  mkStr ns = Fix $ NStr $ DoubleQuoted [Plain (stringIgnoreContext ns)]

prettyNValue
  :: forall t f m ann . MonadDataContext f m => NValue t f m -> Doc ann
prettyNValue = prettyNix . valueToExpr

prettyNValueProv
  :: forall t f m ann
   . ( HasCitations m (NValue t f m) t
     , HasCitations1 m (NValue t f m) f
     , MonadThunk t m (NValue t f m)
     , MonadDataContext f m
     )
  => NValue t f m
  -> Doc ann
prettyNValueProv v = do
  let ps = citations @m @(NValue t f m) v
  case ps of
    [] -> prettyNValue v
    ps ->
      let v' = prettyNValue v in
      fillSep
        [ v'
        , indent 2
        $ parens
        $ mconcat
        $ "from: "
        : map (prettyOriginExpr . _originExpr) ps
        ]

prettyNThunk
  :: forall t f m ann
   . ( HasCitations m (NValue t f m) t
     , HasCitations1 m (NValue t f m) f
     , MonadThunk t m (NValue t f m)
     , MonadDataContext f m
     )
  => t
  -> m (Doc ann)
prettyNThunk t = do
  let ps = citations @m @(NValue t f m) @t t
  v' <- prettyNValue <$> dethunk t
  pure
    $ fillSep
    $ [ v'
      , indent 2
      $ parens
      $ mconcat
      $ "thunk from: "
      : map (prettyOriginExpr . _originExpr) ps
      ]

-- | This function is used only by the testing code.
printNix :: forall t f m . MonadDataContext f m => NValue t f m -> String
printNix = iterNValue (\_ _ -> thk) phi
 where
  thk = "<thunk>"

  phi :: NValue' t f m String -> String
  phi (NVConstant' a ) = unpack $ atomText a
  phi (NVStr'      ns) = show $ stringIgnoreContext ns
  phi (NVList'     l ) = "[ " ++ unwords l ++ " ]"
  phi (NVSet' s _) =
    "{ "
      ++ concat
           [ check (unpack k) ++ " = " ++ v ++ "; "
           | (k, v) <- sort $ map (first unintern) $ toList s
           ]
      ++ "}"
   where
    check v = fromMaybe
      v
      (   fmap (surround . show) (readMaybe v :: Maybe Int)
      <|> fmap (surround . show) (readMaybe v :: Maybe Float)
      )
      where surround s = "\"" ++ s ++ "\""
  phi NVClosure'{}        = "<<lambda>>"
  phi (NVPath' fp       ) = fp
  phi (NVBuiltin' name _) = "<<builtin " ++ show name ++ ">>"
  phi _                   = error "Pattern synonyms foil completeness check"
