{-# LANGUAGE ScopedTypeVariables #-}

module NixLanguageTests (genTests) where

import           Control.Exception
import           GHC.Err                        ( errorWithoutStackTrace )
import           Control.Monad.ST
import           Data.List                      ( delete )
import           Data.List.Split                ( splitOn )
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set
import qualified Data.String                   as String
import qualified Data.Text                     as Text
import qualified Data.Text.IO                  as Text
import           Data.Time
import           GHC.Exts
import           Nix.Lint
import           Nix.Options
import           Nix.Options.Parser
import           Nix.Parser
import           Nix.Pretty
import           Nix.String
import           Nix.XML
import qualified Options.Applicative           as Opts
import           System.Environment
import           System.FilePath
import           System.FilePath.Glob           ( compile
                                                , globDir1
                                                )
import           Test.Tasty
import           Test.Tasty.HUnit
import           TestCommon

{-
From (git://nix)/tests/lang.sh we see that

    lang/parse-fail-*.nix -> parsing should fail
    lang/parse-okay-*.nix -> parsing should succeed
    lang/eval-fail-*.nix -> eval should fail

    lang/eval-okay-*.{nix,xml} -> eval should succeed,
        xml dump should be the same as the .xml
    lang/eval-okay-*.{nix,exp} -> eval should succeed,
        plain text output should be the same as the .exp
    lang/eval-okay-*.{nix,exp,flags} -> eval should succeed,
        plain text output should be the same as the .exp,
        pass the extra flags to nix-instantiate

    NIX_PATH=lang/dir3:lang/dir4 should be in the environment of all
        eval-okay-*.nix evaluations
    TEST_VAR=foo should be in all the environments # for eval-okay-getenv.nix
-}

groupBy :: Ord k => (v -> k) -> [v] -> Map k [v]
groupBy key = Map.fromListWith (<>) . fmap (key &&& pure)

-- | New tests, which have never yet passed.  Once any of these is passing,
-- please remove it from this list.  Do not add tests to this list if they have
-- previously passed.
newFailingTests :: Set String
newFailingTests = Set.fromList
  [ "eval-okay-hash"
  , "eval-okay-hashfile"
  , "eval-okay-path"  -- #128
  , "eval-okay-types"
  , "eval-okay-fromTOML"
  ]

genTests :: IO TestTree
genTests = do
  testFiles <-
    sort
    -- Disabling the not yet done tests cases.
    . filter ((`Set.notMember` newFailingTests) . takeBaseName)
    . filter ((/= ".xml") . takeExtension)
    <$> globDir1 (compile "*-*-*.*") "data/nix/tests/lang"
  let
    testsByName = groupBy (takeFileName . dropExtensions) testFiles
    testsByType = groupBy testType (Map.toList testsByName)
    testGroups  = mkTestGroup <$> Map.toList testsByType
  pure $ localOption (mkTimeout 2000000) $
    testGroup
      "Nix (upstream) language tests"
      testGroups
 where
  testType (fullpath, _files) = take 2 $ splitOn "-" $ takeFileName fullpath
  mkTestGroup (kind, tests) =
    testGroup (String.unwords kind) $ mkTestCase kind <$> tests
  mkTestCase kind (basename, files) = testCase (takeFileName basename) $ do
    time <- liftIO getCurrentTime
    let opts = defaultOptions time
    case kind of
      ["parse", "okay"] -> assertParse opts $ the files
      ["parse", "fail"] -> assertParseFail opts $ the files
      ["eval" , "okay"] -> assertEval opts files
      ["eval" , "fail"] -> assertEvalFail $ the files
      _                 -> fail $ "Unexpected: " <> show kind

assertParse :: Options -> FilePath -> Assertion
assertParse _opts file =
  do
    x <- parseNixFileLoc file
    either
      (\ err -> assertFailure $ "Failed to parse " <> file <> ":\n" <> show err)
      (const pass)  -- pure $! runST $ void $ lint opts expr
      x

assertParseFail :: Options -> FilePath -> Assertion
assertParseFail opts file = do
  eres <- parseNixFileLoc file
  (`catch` \(_ :: SomeException) -> pass)
    (either
      (const pass)
      (\ expr ->
        do
          _ <- pure $! runST $ void $ lint opts expr
          assertFailure $ "Unexpected success parsing `" <> file <> ":\nParsed value: " <> show expr
      )
      eres
    )

assertLangOk :: Options -> FilePath -> Assertion
assertLangOk opts file = do
  actual   <- printNix <$> hnixEvalFile opts (file <> ".nix")
  expected <- Text.readFile $ file <> ".exp"
  assertEqual "" expected $ toText (actual <> "\n")

assertLangOkXml :: Options -> FilePath -> Assertion
assertLangOkXml opts file = do
  actual <- stringIgnoreContext . toXML <$> hnixEvalFile opts (file <> ".nix")
  expected <- Text.readFile $ file <> ".exp.xml"
  assertEqual "" expected actual

assertEval :: Options -> [FilePath] -> Assertion
assertEval _opts files =
  do
    time <- liftIO getCurrentTime
    let opts = defaultOptions time
    case delete ".nix" $ sort $ toText . takeExtensions <$> files of
      []                 -> void $ hnixEvalFile opts (name <> ".nix")
      [".exp"          ]  -> assertLangOk    opts name
      [".exp.xml"      ]  -> assertLangOkXml opts name
      [".exp.disabled" ]  -> pass
      [".exp-disabled" ]  -> pass
      [".exp", ".flags"] ->
        do
          liftIO $ setEnv "NIX_PATH" "lang/dir4:lang/dir5"
          flags <- Text.readFile $ name <> ".flags"
          let flags' | Text.last flags == '\n' = Text.init flags
                    | otherwise               = flags
          case runParserGetResult time flags' of
            Opts.Failure           err   -> errorWithoutStackTrace $ "Error parsing flags from " <> name <> ".flags: " <> show err
            Opts.CompletionInvoked _     -> fail "unused"
            Opts.Success           opts' -> assertLangOk opts' name
      _ -> assertFailure $ "Unknown test type " <> show files
 where
  runParserGetResult time flags' =
    Opts.execParserPure
      Opts.defaultPrefs
      (nixOptionsInfo time)
      (fmap toString $ fixup $ Text.splitOn " " flags')

  name =
    "data/nix/tests/lang/" <> the (takeFileName . dropExtensions <$> files)

  fixup :: [Text] -> [Text]
  fixup ("--arg"    : x : y : rest) = "--arg"    : (x <> "=" <> y) : fixup rest
  fixup ("--argstr" : x : y : rest) = "--argstr" : (x <> "=" <> y) : fixup rest
  fixup (x                  : rest) =                          x  : fixup rest
  fixup []                          = mempty

assertEvalFail :: FilePath -> Assertion
assertEvalFail file = (`catch` (\(_ :: SomeException) -> pass)) $ do
  time       <- liftIO getCurrentTime
  evalResult <- printNix <$> hnixEvalFile (defaultOptions time) file
  evalResult `seq` assertFailure $ "File: ''" <> file <> "'' should not evaluate.\nThe evaluation result was `" <> evalResult <> "`."
