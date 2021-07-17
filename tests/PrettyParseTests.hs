{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NoMonomorphismRestriction #-}



module PrettyParseTests where

import           Data.Algorithm.Diff
import           Data.Algorithm.DiffOutput
import           Data.Char
import           Data.Fix
import qualified Data.String                   as String
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
asciiText = toText <$> asciiString

-- Might want to replace this instance with a constant value
genPos :: Gen Pos
genPos = mkPos <$> Gen.int (Range.linear 1 256)

genSourcePos :: Gen SourcePos
genSourcePos =
  liftA3 SourcePos
    asciiString
    genPos
    genPos

genKeyName :: Gen (NKeyName NExpr)
genKeyName =
  Gen.choice [DynamicKey <$> genAntiquoted genString, StaticKey . coerce <$> asciiText]

genAntiquoted :: Gen a -> Gen (Antiquoted a NExpr)
genAntiquoted gen =
  Gen.choice [Plain <$> gen, pure EscapedNewline, Antiquoted <$> genExpr]

genBinding :: Gen (Binding NExpr)
genBinding = Gen.choice
  [ liftA3 NamedVar
      genAttrPath
      genExpr
      genSourcePos
  , liftA3 Inherit
      (Gen.maybe genExpr)
      (Gen.list (Range.linear 0 5) genKeyName)
      genSourcePos
  ]

genString :: Gen (NString NExpr)
genString = Gen.choice
  [ DoubleQuoted <$> Gen.list (Range.linear 0 5) (genAntiquoted asciiText)
  , liftA2 Indented
      (Gen.int (Range.linear 0 10))
      (Gen.list
        (Range.linear 0 5)
        (genAntiquoted asciiText)
      )
  ]

genAttrPath :: Gen (NAttrPath NExpr)
genAttrPath =
  liftA2 (:|)
    genKeyName
    $ Gen.list (Range.linear 0 4) genKeyName

genParams :: Gen (Params NExpr)
genParams = Gen.choice
  [ Param . coerce <$> asciiText
  , liftA3 (\ a b c -> ParamSet (coerce a) b (coerce <$> c))
      (Gen.list (Range.linear 0 10) (liftA2 (,) asciiText $ Gen.maybe genExpr))
      Gen.bool
      (Gen.choice [stub, pure <$> asciiText])
  ]

genAtom :: Gen NAtom
genAtom = Gen.choice
  [ NInt   <$> Gen.integral (Range.linear     0   1000  )
  , NFloat <$> Gen.float    (Range.linearFrac 0.0 1000.0)
  , NBool  <$> Gen.bool
  , pure NNull
  ]

-- This is written by hand so we can use `fairList` rather than the normal
-- list Arbitrary instance which makes the generator terminate. The
-- distribution is not scientifically chosen.
genExpr :: Gen NExpr
genExpr =
  Gen.sized $
    \(Size n) -> Fix <$>
      if n < 2
        then Gen.choice [genConstant, genStr, genSym, genLiteralPath, genEnvPath]
        else Gen.frequency
          [ (1 , genConstant)
          , (1 , genSym)
          , (4 , Gen.resize (Size (n `div` 3)) genIf)
          , (10, genRecSet)
          , (20, genSet)
          , (5 , genList)
          , (2 , genUnary)
          , (2 , Gen.resize (Size (n `div` 3)) genBinary)
          , (3 , Gen.resize (Size (n `div` 3)) genSelect)
          , (20, Gen.resize (Size (n `div` 2)) genAbs)
          , (2 , Gen.resize (Size (n `div` 2)) genHasAttr)
          , (10, Gen.resize (Size (n `div` 2)) genLet)
          , (10, Gen.resize (Size (n `div` 2)) genWith)
          , (1 , Gen.resize (Size (n `div` 2)) genAssert)
          ]
 where
  genConstant    = NConstant                <$> genAtom
  genStr         = NStr                     <$> genString
  genSym         = NSym . coerce            <$> asciiText
  genList        = NList                    <$> fairList genExpr
  genSet         = NSet NonRecursive        <$> fairList genBinding
  genRecSet      = NSet Recursive           <$> fairList genBinding
  genLiteralPath = NLiteralPath . ("./" <>) <$> asciiString
  genEnvPath     = NEnvPath                 <$> asciiString
  genUnary       = liftA2 NUnary   Gen.enumBounded       genExpr
  genBinary      = liftA3 NBinary  Gen.enumBounded       genExpr     genExpr
  genSelect      = liftA3 NSelect  (Gen.maybe genExpr)   genExpr     genAttrPath
  genHasAttr     = liftA2 NHasAttr genExpr               genAttrPath
  genAbs         = liftA2 NAbs     genParams             genExpr
  genLet         = liftA2 NLet     (fairList genBinding) genExpr
  genIf          = liftA3 NIf      genExpr               genExpr     genExpr
  genWith        = liftA2 NWith    genExpr               genExpr
  genAssert      = liftA2 NAssert  genExpr               genExpr

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
    mkNeg $ mkInt $ negate n
  NConstant (NFloat n) | n < 0 ->
    mkNeg $ mkFloat $ negate n

  NSet recur binds ->
    mkSet recur $ normBinding <$> binds
  NLet binds  r ->
    mkLets (normBinding <$> binds) r

  NAbs params r ->
    mkFunction (normParams params) r

  r             -> Fix r

 where
  normBinding (NamedVar path r     pos) = NamedVar (normKey <$> path) r pos
  normBinding (Inherit  mr   names pos) = Inherit mr (normKey <$> names) pos

  normKey (DynamicKey quoted) = DynamicKey (normAntiquotedString quoted)
  normKey (StaticKey  name  ) = StaticKey name

  normAntiquotedString
    :: Antiquoted (NString NExpr) NExpr
    -> Antiquoted (NString NExpr) NExpr
  normAntiquotedString (Plain (DoubleQuoted [EscapedNewline])) = EscapedNewline
  normAntiquotedString (Plain (DoubleQuoted strs)) =
    bool normAntiquotedString id (strs == strs')
      (Plain $ DoubleQuoted strs')
    where
     strs' = normAntiquotedText <$> strs
  normAntiquotedString r = r

  normAntiquotedText
    :: Antiquoted Text NExpr
    -> Antiquoted Text NExpr
  normAntiquotedText (Plain "\n"  ) = EscapedNewline
  normAntiquotedText (Plain "''\n") = EscapedNewline
  normAntiquotedText r              = r

  normParams (ParamSet binds var (Just "")) = ParamSet binds var (coerce @Text <$> mempty)
  normParams r                              = r

-- | Test that parse . pretty == id up to attribute position information.
prop_prettyparse :: Monad m => NExpr -> PropertyT m ()
prop_prettyparse p = do
  let prog = show $ prettyNix p
  either
    (\ s -> do
      footnote $ show $ vsep
        -- Remove :: Text type annotation after String -> Text migration.
        [fillSep ["Parse failed:", pretty (show s :: Text)], indent 2 $ prettyNix p]
      discard
    )
    (\ v ->
      bool
        (do
          let
            pp = normalise prog
            pv = normalise $ show $ prettyNix v

          footnote $
            show $
              vsep
                [ "----------------------------------------"
                , vsep ["Expr before:"      , indent 2 $ pretty $ PS.ppShow p]
                , "----------------------------------------"
                , vsep ["Expr after:"       , indent 2 $ pretty $ PS.ppShow v]
                , "----------------------------------------"
                , vsep ["Pretty before:"    , indent 2 $ pretty prog]
                , "----------------------------------------"
                , vsep ["Pretty after:"     , indent 2 $ prettyNix v]
                , "----------------------------------------"
                , vsep ["Normalised before:", indent 2 $ pretty pp]
                , "----------------------------------------"
                , vsep ["Normalised after:" , indent 2 $ pretty pv]
                , "========================================"
                , vsep ["Normalised diff:"  , pretty $ ppDiff $ ldiff pp pv]
                , "========================================"
                ]
          assert (pp == pv)
        )
        success
        (equivUpToNormalization p v)
    )
    (parse $ toText prog)
 where
  parse     = parseNixText

  normalise s = String.unlines $ reverse . dropWhile isSpace . reverse <$> String.lines s

  ldiff :: String -> String -> [Diff [String]]
  ldiff s1 s2 = getDiff ((: mempty) <$> String.lines s1) ((: mempty) <$> String.lines s2)

tests :: TestLimit -> TestTree
tests n = testProperty "Pretty/Parse Property" $ withTests n $ property $ do
  x <- forAll genExpr
  prop_prettyparse x
