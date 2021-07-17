{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}


module ParserTests (tests) where

import Prelude hiding (($<))
import Data.Fix
import NeatInterpolation (text)
import Nix.Atoms
import Nix.Expr
import Nix.Parser
import Nix.Pretty
import Prettyprinter
import Prettyprinter.Render.Text
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

default (NixLang)

-- * Tests


-- ** Literals

case_constant_int =
  checks
    ( mkInt 234
    , "234"
    )

case_constant_bool = do
  checks
    ( mkBool True
    , "true"
    )
    ( mkBool False
    , "false"
    )

case_constant_bool_respects_attributes = do
  invariantVals
    "true-foo"
    "false-bar"

case_constant_path_invariants =
  knownAs (staysInvariantUnder (mkRelPath . toString))
    "./."
    "./+-_/cdef/09ad+-"
    "/abc"
    "../abc"
    "~/a"
    "~/a/b"
    "a/b"
    "4/2"
    "rec+def/cdef"

case_constant_path =
  checks
    ( var "a'b" @@ mkRelPath "/c"
    , "a'b/c"
    )
    ( mkRelPath "a/b" $// mkRelPath "c/def" $// mkEnvPath "g" $<  mkRelPath "def/d"
    , "a/b//c/def//<g> < def/d"
    )
    ( mkEnvPath "abc"
    , "<abc>"
    )
    ( mkEnvPath "../cdef"
    , "<../cdef>"
    )
    ( var "a" $// var "b"
    , "a//b"
    )

case_constant_path_syntax_mistakes =
  mistakes
    "."
    ".."
    "/"
    "a/"
    "a/def/"
    "~"
    "~/"

case_constant_uri =
  knownAs (staysInvariantUnder mkStr)
    "a:a"
    "http://foo.bar"
    "a+de+.adA+-:%%%ads%5asdk&/"
    "rec+def:c"
    "f.foo:bar"


case_constant_uri_syntax_mistakes =
  mistakes
    "http://foo${\"bar\"}"
    ":bcdef"
    "a%20:asda"
    ".:adasd"
    "+:acdcd"


-- *** Special chars in vals

case_identifier_special_chars =
  invariantVals
    "_a"
    "a_b"
    "a'b"
    "a''b"
    "a-b"
    "a--b"
    "a12a"

case_identifier_special_chars_syntax_mistakes =
  mistakes
    ".a"
    "'a"

-- ** Sets

-- *** Non-recursive sets

case_simple_set =
  checks
    ( mkNonRecSet
        [ "a" $= mkInt 23
        , "b" $= mkInt  4
        ]
    , "{ a = 23; b = 4; }"
    )

case_simple_set_syntax_mistakes =
  mistakes
    "{ a = 23 }"

case_set_complex_keynames =
  checks
    ( mkNonRecSet
        [ NamedVar (DynamicKey (Plain (DoubleQuoted mempty)) :| mempty) mkNull nullPos ]
    , "{ \"\" = null; }"
    )
    ( mkNonRecSet
        [ NamedVar (StaticKey "a" :| [StaticKey "b"]) (mkInt 3) nullPos
        , NamedVar (StaticKey "a" :| [StaticKey "c"]) (mkInt 4) nullPos
        ]
    , "{ a.b = 3; a.c = 4; }"
    )
    ( mkNonRecSet
        [ NamedVar (DynamicKey (Antiquoted letExpr) :| mempty) (mkInt 4) nullPos ]
    , "{ ${let a = \"b\"; in a} = 4; }"
    )
    ( mkNonRecSet
        [ NamedVar (DynamicKey (Plain str) :| [StaticKey "e"]) (mkInt 4) nullPos ]
    , "{ \"a${let a = \"b\"; in a}c\".e = 4; }"
    )
 where
  letExpr = mkLets ["a" $= mkStr "b"] (var "a")
  str = DoubleQuoted [Plain "a", Antiquoted letExpr, Plain "c"]


-- *** Recursivity in sets

case_set_rec =
  checks
    ( mkRecSet
        [ "a" $= mkInt 3
        , "b" $= var "a"
        ]
    , "rec { a = 3; b = a; }"
    )


-- *** Inheritance

case_set_inherit =
  checks
    ( mkNonRecSet
        [ "e" $= mkInt 3
        , inherit (StaticKey <$> ["a", "b"])
        ]
    , "{ e = 3; inherit a b; }"
    )
    ( mkNonRecSet [ inherit mempty ]
    , "{ inherit; }"
    )

case_set_scoped_inherit =
  checks
    ( mkNonRecSet $
        (\ x -> [x, "e" $= mkInt 4, x]) $
          inheritFrom (var "a") (StaticKey <$> ["b", "c"])
    , "{ inherit (a) b c; e = 4; inherit(a)b c; }"
    )

case_set_inherit_direct =
  checks
    ( mkNonRecSet [ inheritFrom (mkNonRecSet ["a" $= mkInt 3]) mempty ]
    , "{ inherit ({a = 3;}); }"
    )

case_inherit_selector =
  checks
    ( mkNonRecSet [inherit [DynamicKey (Plain (DoubleQuoted [Plain "a"]))]]
    , "{ inherit \"a\"; }"
    )

case_inherit_selector_syntax_mistakes =
  mistakes
    "{ inherit a.x; }"


-- ** Lists

case_int_list =
  checks
    ( mkList $ mkInt <$> [1,2,3]
    , "[1 2 3]"
    )

case_int_null_list =
  checks
    ( mkList (mkConst <$> [NInt 1, NInt 2, NInt 3, NNull, NInt 4])
    , "[1 2 3 null 4]"
    )

case_mixed_list =
  checks
    ( mkList
        [ mkNonRecSet ["a" $= mkInt 3] @. "a"
        , mkIf (mkBool True) mkNull (mkBool False)
        , mkNull
        , mkBool False
        , mkInt 4
        , emptyList
        , (@.<|>) (var "c") "d" mkNull
        ]
    , "[{a = 3;}.a (if true then null else false) null false 4 [] c.d or null]"
    )

case_mixed_list_syntax_mistakes =
  mistakes
    "[if true then null else null]"
    "[a ? b]"
    "[a : a]"
    "[${\"test\")]"


-- ** Lambdas

case_simple_lambda =
  checks
    ( mkFunction (Param "a") (var "a")
    , "a: a"
    )

case_lambda_or_uri =
  checks
    ( mkFunction (Param "a") $ var "b"
    , "a :b"
    )
    ( var "a" @@ mkStr "c:def"
    , "a c:def"
    )
    ( mkStr "c:def:" @@ var "c"
    , "c:def: c"
    )
    ( mkFunction (Param "a") emptySet
    , "a:{}"
    )
    ( mkFunction (Param "a") $ mkList [var "a"]
    , "a:[a]"
    )

case_lambda_or_uri_syntax_mistakes =
  mistakes
    "def:"

case_lambda_pattern =
  checks
    ( mkFunction (fixed args Nothing) $ var "b"
    , "{b, c ? 1}: b"
    -- Fix (NAbs (ParamSet [("b",Nothing),("c",Just (Fix (NConstant (NInt 1))))] False Nothing) (Fix (NSym "b")))
    )
    ( mkFunction (fixed args2 Nothing) $ var "b"
    , "{ b ? x: x  }: b"
    )
    ( mkFunction (fixed args $ pure "a") $ var "b"
    , "a@{b,c ? 1}: b"
    )
    ( mkFunction (fixed args $ pure "a") $ var "c"
    , "{b,c?1}@a: c"
    )
    ( mkFunction (variadic vargs $ pure "a") $ var "c"
    , "{b,c?1,...}@a: c"
    )
    ( mkFunction (variadic mempty Nothing) $ mkInt 1
    , "{...}: 1"
    )
 where
  fixed    args = ParamSet args False
  variadic args = ParamSet args True
  args  = [("b", Nothing), ("c", pure $ mkInt 1)]
  vargs = [("b", Nothing), ("c", pure $ mkInt 1)]
  args2 = [("b", pure lam)]
  lam = mkFunction (Param "x") $ var "x"

case_lambda_pattern_syntax_mistakes =
  mistakes
    "a@b: a"
    "{a}@{b}: a"

case_lambda_app_int =
  checks
    ( mkFunction (Param "a") (var "a") @@ mkInt 3
    , "(a: a) 3"
    )


-- ** Let

case_simple_let =
  checks
    ( mkLets ["a" $= mkInt 4] $ var "a"
    , "let a = 4; in a"
    )

case_simple_let_syntax_mistakes =
  mistakes
    "let a = 4 in a"

case_let_body =
  checks
    ( mkRecSet ["body" $= mkInt 1] @. "body"
    , "let { body = 1; }"
    )

case_nested_let =
  checks
    ( mkLets ["a" $= mkInt 4] $
        mkLets ["b" $= mkInt 5] $ var "a"
    , "let a = 4; in let b = 5; in a"
    )

case_nested_let_syntax_mistakes =
  mistakes
    "let a = 4; let b = 3; in b"

case_let_scoped_inherit =
  checks
    ( mkLets
        [ "a" $= mkNull
        , inheritFrom (var "b") [StaticKey "c"]
        ]
        $ var "c"
    , "let a = null; inherit (b) c; in c"
    )

case_let_scoped_inherit_syntax_mistakes =
  mistakes
    "let inherit (b) c in c"


-- ** If

case_if =
  checks
    ( mkIf (mkBool True) (mkBool True) (mkBool False)
    , "if true then true else false"
    )

case_if_syntax_mistakes =
  mistakes
    "if true then false"
    "else"
    "if true then false else"
    "if true then false else false else"
    "1 + 2 then"


-- ** Literal expressions in vals

case_identifier_keyword_prefix_invariants =
  invariantVals
    "true-name"
    "trueName"
    "null-name"
    "nullName"

case_identifier_keyword_prefix =
  checks
    ( mkList [ var "null-name" ]
    , "[ null-name ]"
    )


-- ** Strings

invariantString str =
  checks
    ( mkStr str
    , "\"" <> str <> "\""
    )

case_simple_string =
  knownAs invariantString
    "abcdef"
    "a"
    "A"
    "   a a  "
    ""

case_string_dollar =
  knownAs invariantString
    "a$b"
    "a$$b"
    "$cdef"
    "gh$i"

case_string_escape =
  checks
    ( mkStr "$\n\t\r\\"
    , "\"\\$\\n\\t\\r\\\\\""
    )
    ( mkStr " \" ' "
    , "\" \\\" \\' \""
    )

case_string_antiquote =
  checks
    ( Fix $ NStr $ DoubleQuoted
        [ Plain "abc"
        , Antiquoted $ mkIf (mkBool True) (mkStr "def") (mkStr "abc")
        , Plain " g"
        ]
    , "\"abc${  if true then \"def\" else \"abc\"  } g\""
    )
    ( mkStr "${a}"
    , "\"\\${a}\""
    )

case_string_antiquote_syntax_mistakes =
  mistakes
    "\"a"
    "${true}"
    "\"${true\""


-- *** Indented string

case_indented_string =
  checks
    ( mkIndentedStr 0 "a"
    , "''a''"
    )
    ( mkIndentedStr 2 "foo\nbar"
    , "''\n  foo\n  bar''"
    )
    ( mkIndentedStr 0 ""
    , "''        ''"
    )
    ( mkIndentedStr 0 "''"
    , "'''''''"
    )
    ( Fix $ NStr $ Indented 3
        [ Antiquoted mkNull
        , Plain "\na"
        , Antiquoted mkNull
        ]
    , "''   ${null}\n   a${null}''"
    )

case_indented_string_syntax_mistakes =
  mistakes
    "'''''"
    "''   '"

case_indented_string_escape =
  checks
    ( mkIndentedStr 1 "\n \t \\ ${ \\ \\n ' '' "
    , "'' ''\\n ''\\t ''\\\\ ''${ \\ \\n ' ''' ''"
    )

-- ** Selection

case_select =
  checks
    ( Fix $ NSelect Nothing (var "a") (StaticKey "e" :| [StaticKey "di", StaticKey "f"])
    , "a .  e .di. f"
    )
    ( Fix $ NSelect (pure mkNull) (var "a")
        (StaticKey "e" :| [StaticKey "d"])
    , "a.e . d    or null"
    )
    ( Fix $ NSelect (pure mkNull) emptySet
        (DynamicKey (Plain (DoubleQuoted mempty)) :| mempty)
    , "{}.\"\"or null"
    )
    ( Fix $ NBinary NConcat
        ((@.<|>)
          (mkNonRecSet
            [NamedVar
              (mkSelector "a")
              (mkList $ one $ mkInt 1)
              nullPos
            ]
          )
          "a"
          (mkList $ one $ mkInt 2)
        )
        (mkList $ one $ mkInt 3)
    , "{ a = [1]; }.a or [2] ++ [3]"
    )

case_select_path =
  checks
    ( var "f" @@ mkRelPath "./."
    , "f ./."
    )
    ( var "f" @. "b" @@ mkRelPath "../a"
    , "f.b ../a"
    )
    ( emptySet @@ mkRelPath "./def"
    , "{}./def"
    )
    ( Fix (NSelect Nothing emptySet (DynamicKey (Plain $ DoubleQuoted mempty) :| mempty)) @@ mkRelPath "./def"
    , "{}.\"\"./def"
    )

case_select_keyword =
  checks
    ( mkNonRecSet ["false" $= mkStr "foo"]
    , "{ false = \"foo\"; }"
    )

case_select_or_precedence =
    assertParsePrint [text|let
  matchDef = def:   matcher:
                      v:   let
                             case = builtins.head (builtins.attrNames v);
                           in (matcher.case or def case) (v.case);
in null|] [text|let
  matchDef = def:
    matcher:
      v:
        let
          case = builtins.head (builtins.attrNames v);
        in (matcher.case or def) case (v.case);
in null|]

case_select_or_precedence2 =
    assertParsePrint [text|let
  matchDef = def:   matcher:
                      v:   let
                             case = builtins.head (builtins.attrNames v);
                           in (matcher.case or null.foo) (v.case);
in null|] [text|let
  matchDef = def:
    matcher:
      v:
        let
          case = builtins.head (builtins.attrNames v);
        in (matcher.case or null).foo (v.case);
in null|]

-- ** Function application

case_fun_app =
  checks
    ( var "f" @@ var "a" @@ var "b"
    , "f a b"
    )
    ( var "f" @@ (@.<|>) (var "a") "x" mkNull
    , "f a.x or null"
    )

case_fun_app_syntax_mistakes =
  mistakes
   "f if true then null else null"


-- ** Operators

case_operator_fun_app =
  checks
    ( var "a" $++ var "b"
    , "a ++ b"
    )
    ( var "a" $++ var "f" @@ var "b"
    , "a ++ f b"
    )

case_operators =
  checks
    ( mkInt 1 $+ mkInt 2 $- mkInt 3
    , "1 + 2 - 3"
    )
    ( mkInt 1 $+ mkIf (mkBool True) (mkInt 2) (mkInt 3)
    , "1 + (if true then 2 else 3)"
    )
    ( mkNonRecSet ["a" $= mkInt 3] $// mkRecSet ["b" $= mkInt 4]
    , "{ a = 3; } // rec { b = 4; }"
    )
    ( mkNeg $ mkNeg $ var "a"
    , "--a"
    )
    ( var "a" $- var "b" $- var "c"
    , "a - b - c"
    )
    ( var "foo" $< var "bar"
    , "foo<bar"
    )

case_operators_syntax_mistakes =
  mistakes
    "+ 3"
    "foo +"
    "1 + if true then 1 else 2"


-- ** Comments

case_comments =
  do
    Right expected <- parseNixFile "data/let.nix"
    assertParseFile "let-comments-multiline.nix" expected
    assertParseFile "let-comments.nix" expected


-- ** Location

case_simpleLoc =
  let
    mkSPos l c = SourcePos "<string>" (mkPos l) (mkPos c)
    mkSpan l1 c1 l2 c2 = SrcSpan (mkSPos l1 c1) (mkSPos l2 c2)
  in
    assertParseTextLoc [text|let
    foo = bar
         baz "qux";
    in foo
    |]
    (Fix
      (NLet_
        (mkSpan 1 1 4 7)
        [ NamedVar
            (StaticKey "foo" :| [])
            (Fix
              (NBinary_
                (mkSpan 2 7 3 15)
                NApp
                (Fix
                  (NBinary_
                    (mkSpan 2 7 3 9)
                    NApp
                    (Fix (NSym_ (mkSpan 2 7 2 10) "bar"))
                    (Fix (NSym_ (mkSpan 3 6 3 9) "baz"))
                  )
                )
                (Fix (NStr_ (mkSpan 3 10 3 15) (DoubleQuoted [Plain "qux"])))
              )
            )
            (mkSPos 2 1)
        ]
        (Fix (NSym_ (mkSpan 4 4 4 7) "foo"))
      )
    )


tests :: TestTree
tests = $testGroupGenerator

---------------------------------------------------------------------------------

-- * Helpers

var = mkSym

invariantVal = staysInvariantUnder var

staysInvariantUnder :: (NixLang -> ExpectedHask) -> NixLang -> Assertion
staysInvariantUnder f v =
  (<=>) (f v) v

type NixLang = Text
type ExpectedHask = NExpr

(<=>) :: ExpectedHask -> NixLang -> Assertion
(<=>) = assertParseText

throwParseError
  :: ( IsString a
    , ToString a
    , Semigroup a
    , Show b
    )
  => a -> a -> b -> IO c
throwParseError what str err = assertFailure $ toString $ "Unexpected fail parsing " <> what <> ":\n  ''\n" <> str <> "\n''\n  Error: ''" <> show err <> "''."

assertParseText :: ExpectedHask -> NixLang -> Assertion
assertParseText expected str =
  either
    (throwParseError "expression" str)
    (assertEqual
      ("When parsing " <> toString str)
      (stripPositionInfo expected)
      . stripPositionInfo
    )
    (parseNixText str)

assertParseTextLoc :: NixLang -> NExprLoc -> Assertion
assertParseTextLoc str expected =
  either
    (throwParseError "expression" str)
    (assertEqual
      ("When parsing " <> toString str)
      expected
    )
    (parseNixTextLoc str)

assertParseFile :: FilePath -> NExpr -> Assertion
assertParseFile file expected =
  do
  res <- parseNixFile $ "data/" <> file
  either
    (throwParseError "data file" file)
    (assertEqual
      ("Parsing data file " <> file)
      (stripPositionInfo expected)
      . stripPositionInfo
    )
    res

assertParseFail :: NixLang -> Assertion
assertParseFail str =
  either
    (const pass)
    (\ r ->
      assertFailure $ toString $ "Unexpected success parsing ''" <> str <> "'':\n  Parsed value: ''" <> show r <> "''."
    )
    (parseNixText str)

-- assertRoundTrip :: Text -> Assertion
-- assertRoundTrip src = assertParsePrint src src

assertParsePrint :: Text -> Text -> Assertion
assertParsePrint src expect =
  let
    Right expr = parseNixTextLoc src
    result =
      renderStrict
      . layoutPretty (LayoutOptions $ AvailablePerLine 80 0.4)
      . prettyNix
      . stripAnnotation $
        expr
  in assertEqual "" expect result


-----

-- | This class constructs functions that accept variacic number of argumets.
-- Every argument is an assertion.
-- So now the new assertions can be added just by adding it to a block of according assertions.
class VariadicAssertions t where
  checkListPairs' :: ((ExpectedHask, NixLang) -> Assertion) -> [(ExpectedHask, NixLang)] -> t

instance VariadicAssertions (IO a) where
  checkListPairs' f acc =
    do
      traverse_ f acc
      pure $ error "never would be reached, cuz `I'm lazy`."

instance (VariadicAssertions a) => VariadicAssertions ((ExpectedHask, NixLang) -> a) where
  checkListPairs' f acc x = checkListPairs' f (acc <> [x])

checks :: (VariadicAssertions a) => a
checks = checkListPairs' (uncurry assertParseText) []


class VariadicArgs t where
  checkList' :: (NixLang -> Assertion) -> [NixLang] -> t

instance VariadicArgs (IO a) where
  checkList' f acc =
    do
      traverse_ f acc
      pure $ error "never would be reached, cuz `I'm lazy`."

instance (VariadicArgs a) => VariadicArgs (NixLang -> a) where
  checkList' f acc x = checkList' f (acc <> [x])

knownAs :: (VariadicArgs a) => (NixLang -> Assertion) -> a
knownAs f = checkList' f []

mistakes :: (VariadicArgs a) => a
mistakes = knownAs assertParseFail

invariantVals :: (VariadicArgs a) => a
invariantVals = knownAs invariantVal

