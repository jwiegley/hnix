{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS -Wno-orphans#-}

module PrettyParseTests where

import           Data.Algorithm.Diff
import           Data.Algorithm.DiffOutput
import           Data.Char
import           Data.Fix
import           Data.Interned
import qualified Data.List.NonEmpty            as NE
import           Data.Text                      ( Text
                                                , pack
                                                )
import           Hedgehog
import qualified Hedgehog.Gen                  as Gen
import qualified Hedgehog.Range                as Range
import           Nix.Atoms
import           Nix.Expr
import           Nix.Parser
import           Nix.Pretty
import           Nix.Utils
import           Prettyprinter
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Text.Megaparsec                ( Pos )
import qualified Text.Show.Pretty              as PS

asciiString :: MonadGen m => m String
asciiString = Gen.list (Range.linear 1 15) Gen.lower

asciiText :: Gen Text
asciiText = pack <$> asciiString

asciiVarName :: Gen VarName
asciiVarName = intern <$> asciiText

-- Might want to replace this instance with a constant value
genPos :: Gen Pos
genPos = mkPos <$> Gen.int (Range.linear 1 256)

genSourcePos :: Gen SourcePos
genSourcePos = SourcePos <$> asciiString <*> genPos <*> genPos

genKeyName :: Gen (NKeyName NExpr)
genKeyName =
  Gen.choice [DynamicKey <$> genAntiquoted genString, StaticKey <$> asciiVarName]

genAntiquoted :: Gen a -> Gen (Antiquoted a NExpr)
genAntiquoted gen =
  Gen.choice [Plain <$> gen, pure EscapedNewline, Antiquoted <$> genExpr]

genBinding :: Gen (Binding NExpr)
genBinding = Gen.choice
  [ NamedVar <$> genAttrPath <*> genExpr <*> genSourcePos
  , Inherit
  <$> Gen.maybe genExpr
  <*> Gen.list (Range.linear 0 5) genKeyName
  <*> genSourcePos
  ]

genString :: Gen (NString NExpr)
genString = Gen.choice
  [ DoubleQuoted <$> Gen.list (Range.linear 0 5) (genAntiquoted asciiText)
  , Indented <$> Gen.int (Range.linear 0 10) <*> Gen.list
    (Range.linear 0 5)
    (genAntiquoted asciiText)
  ]

genAttrPath :: Gen (NAttrPath NExpr)
genAttrPath = (NE.:|) <$> genKeyName <*> Gen.list (Range.linear 0 4) genKeyName

genParams :: Gen (Params NExpr)
genParams = Gen.choice
  [ Param <$> asciiVarName
  , ParamSet
  <$> Gen.list (Range.linear 0 10) ((,) <$> asciiVarName <*> Gen.maybe genExpr)
  <*> Gen.bool
  <*> Gen.choice [pure Nothing, Just <$> asciiVarName]
  ]

genAtom :: Gen NAtom
genAtom = Gen.choice
  [ NInt <$> Gen.integral (Range.linear 0 1000)
  , NFloat <$> Gen.float (Range.linearFrac 0.0 1000.0)
  , NBool <$> Gen.bool
  , pure NNull
  ]

-- This is written by hand so we can use `fairList` rather than the normal
-- list Arbitrary instance which makes the generator terminate. The
-- distribution is not scientifically chosen.
genExpr :: Gen NExpr
genExpr = Gen.sized $ \(Size n) -> Fix <$> if n < 2
  then Gen.choice [genConstant, genStr, genSym, genLiteralPath, genEnvPath]
  else Gen.frequency
    [ (1 , genConstant)
    , (1 , genSym)
    , (4 , Gen.resize (Size (n `div` 3)) genIf)
    , (10, genRecSet)
    , (20, genSet)
    , (5 , genList)
    , (2 , genUnary)
    , (2, Gen.resize (Size (n `div` 3)) genBinary)
    , (3, Gen.resize (Size (n `div` 3)) genSelect)
    , (20, Gen.resize (Size (n `div` 2)) genAbs)
    , (2, Gen.resize (Size (n `div` 2)) genHasAttr)
    , (10, Gen.resize (Size (n `div` 2)) genLet)
    , (10, Gen.resize (Size (n `div` 2)) genWith)
    , (1, Gen.resize (Size (n `div` 2)) genAssert)
    ]
 where
  genConstant    = NConstant <$> genAtom
  genStr         = NStr <$> genString
  genSym         = NSym <$> asciiVarName
  genList        = NList <$> fairList genExpr
  genSet         = NSet NNonRecursive <$> fairList genBinding
  genRecSet      = NSet NRecursive <$> fairList genBinding
  genLiteralPath = NLiteralPath . ("./" ++) <$> asciiString
  genEnvPath     = NEnvPath <$> asciiString
  genUnary       = NUnary <$> Gen.enumBounded <*> genExpr
  genBinary      = NBinary <$> Gen.enumBounded <*> genExpr <*> genExpr
  genSelect      = NSelect <$> genExpr <*> genAttrPath <*> Gen.maybe genExpr
  genHasAttr     = NHasAttr <$> genExpr <*> genAttrPath
  genAbs         = NAbs <$> genParams <*> genExpr
  genLet         = NLet <$> fairList genBinding <*> genExpr
  genIf          = NIf <$> genExpr <*> genExpr <*> genExpr
  genWith        = NWith <$> genExpr <*> genExpr
  genAssert      = NAssert <$> genExpr <*> genExpr

-- | Useful when there are recursive positions at each element of the list as
--   it divides the size by the length of the generated list.
fairList :: Gen a -> Gen [a]
fairList g = Gen.sized $ \s -> do
  k <- Gen.int (Range.linear 0 (unSize s))
  -- Use max here to avoid dividing by zero when there is the empty list
  Gen.resize (Size (unSize s `div` max 1 k)) $ Gen.list (Range.singleton k) g

equivUpToNormalization :: NExpr -> NExpr -> Bool
equivUpToNormalization x y = normalize x == normalize y

normalize :: NExpr -> NExpr
normalize = foldFix $ \case
  NConstant (NInt n) | n < 0 ->
    Fix (NUnary NNeg (Fix (NConstant (NInt (negate n)))))
  NConstant (NFloat n) | n < 0 ->
    Fix (NUnary NNeg (Fix (NConstant (NFloat (negate n)))))

  NSet recur binds -> Fix (NSet recur (map normBinding binds))
  NLet binds  r -> Fix (NLet (map normBinding binds) r)

  NAbs params r -> Fix (NAbs (normParams params) r)

  r             -> Fix r

 where
  normBinding (NamedVar path r     pos) = NamedVar (NE.map normKey path) r pos
  normBinding (Inherit  mr   names pos) = Inherit mr (map normKey names) pos

  normKey (DynamicKey quoted) = DynamicKey (normAntiquotedString quoted)
  normKey (StaticKey  name  ) = StaticKey name

  normAntiquotedString
    :: Antiquoted (NString NExpr) NExpr -> Antiquoted (NString NExpr) NExpr
  normAntiquotedString (Plain (DoubleQuoted [EscapedNewline])) = EscapedNewline
  normAntiquotedString (Plain (DoubleQuoted strs)) =
    let strs' = map normAntiquotedText strs
    in  if strs == strs'
          then Plain (DoubleQuoted strs)
          else normAntiquotedString (Plain (DoubleQuoted strs'))
  normAntiquotedString r = r

  normAntiquotedText :: Antiquoted Text NExpr -> Antiquoted Text NExpr
  normAntiquotedText (Plain "\n"  ) = EscapedNewline
  normAntiquotedText (Plain "''\n") = EscapedNewline
  normAntiquotedText r              = r

  normParams (ParamSet binds var (Just "")) = ParamSet binds var Nothing
  normParams r                              = r

-- | Test that parse . pretty == id up to attribute position information.
prop_prettyparse :: Monad m => NExpr -> PropertyT m ()
prop_prettyparse p = do
  let prog = show (prettyNix p)
  case parse (pack prog) of
    Failure s -> do
      footnote $ show $ vsep
        [fillSep ["Parse failed:", pretty (show s)], indent 2 (prettyNix p)]
      discard
    Success v
      | equivUpToNormalization p v -> success
      | otherwise -> do
        let pp = normalise prog
            pv = normalise (show (prettyNix v))
        footnote
          $ show
          $ vsep
          $ [ "----------------------------------------"
            , vsep ["Expr before:", indent 2 (pretty (PS.ppShow p))]
            , "----------------------------------------"
            , vsep ["Expr after:", indent 2 (pretty (PS.ppShow v))]
            , "----------------------------------------"
            , vsep ["Pretty before:", indent 2 (pretty prog)]
            , "----------------------------------------"
            , vsep ["Pretty after:", indent 2 (prettyNix v)]
            , "----------------------------------------"
            , vsep ["Normalised before:", indent 2 (pretty pp)]
            , "----------------------------------------"
            , vsep ["Normalised after:", indent 2 (pretty pv)]
            , "========================================"
            , vsep ["Normalised diff:", pretty (ppDiff (ldiff pp pv))]
            , "========================================"
            ]
        assert (pp == pv)
 where
  parse     = parseNixText

  normalise = unlines . map (reverse . dropWhile isSpace . reverse) . lines

  ldiff :: String -> String -> [Diff [String]]
  ldiff s1 s2 = getDiff (map (: []) (lines s1)) (map (: []) (lines s2))

tests :: TestLimit -> TestTree
tests n = testProperty "Pretty/Parse Property" $ withTests n $ property $ do
  x <- forAll genExpr
  prop_prettyparse x
