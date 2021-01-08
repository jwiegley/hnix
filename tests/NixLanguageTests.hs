{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module NixLanguageTests (genTests) where

import           Control.Arrow                  ( (&&&) )
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Data.List                      ( delete
                                                , sort
                                                )
import           Data.List.Split                ( splitOn )
import           Data.Map                       ( Map )
import qualified Data.Map                      as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import qualified Data.Text                     as Text
import qualified Data.Text.IO                  as Text
import           Data.Time
import           GHC.Exts
--import           Nix.Lint
import           Nix.Options
import           Nix.Options.Parser
import           Nix.Parser
import           Nix.Pretty
import           Nix.String
import           Nix.Utils
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
groupBy key = Map.fromListWith (++) . map (key &&& pure)

-- | New tests, which have never yet passed.  Once any of these is passing,
-- please remove it from this list.  Do not add tests to this list if they have
-- previously passed.
newFailingTests :: Set String
newFailingTests = Set.fromList
  [ "eval-okay-hash"
  , "eval-okay-hashfile"
  , "eval-okay-path"
  , "eval-okay-types"
  , "eval-okay-fromTOML"
  , "eval-okay-context-introspection"
  ]

genTests :: IO TestTree
genTests = do
  testFiles <-
    sort
        -- jww (2018-05-07): Temporarily disable this test until #128 is fixed.
    .   filter ((`Set.notMember` newFailingTests) . takeBaseName)
    .   filter ((/= ".xml") . takeExtension)
    <$> globDir1 (compile "*-*-*.*") "data/nix/tests/lang"
  let testsByName = groupBy (takeFileName . dropExtensions) testFiles
  let testsByType = groupBy testType (Map.toList testsByName)
  let testGroups  = map mkTestGroup (Map.toList testsByType)
  pure $ localOption (mkTimeout 2000000) $ testGroup
    "Nix (upstream) language tests"
    testGroups
 where
  testType (fullpath, _files) = take 2 $ splitOn "-" $ takeFileName fullpath
  mkTestGroup (kind, tests) =
    testGroup (unwords kind) $ map (mkTestCase kind) tests
  mkTestCase kind (basename, files) = testCase (takeFileName basename) $ do
    time <- liftIO getCurrentTime
    let opts = defaultOptions time
    case kind of
      ["parse", "okay"] -> assertParse opts $ the files
      ["parse", "fail"] -> assertParseFail opts $ the files
      ["eval" , "okay"] -> assertEval opts files
      ["eval" , "fail"] -> assertEvalFail $ the files
      _                 -> error $ "Unexpected: " ++ show kind

assertParse :: Options -> FilePath -> Assertion
assertParse _opts file = parseNixFileLoc file >>= \case
  Success _expr -> pure () -- pure $! runST $ void $ lint opts expr
  Failure err ->
    assertFailure $ "Failed to parse " ++ file ++ ":\n" ++ show err

assertParseFail :: Options -> FilePath -> Assertion
assertParseFail opts file = do
  eres <- parseNixFileLoc file
  catch
      (case eres of
        Success expr -> do
        --  _ <- pure $! runST $ void $ lint opts expr
          assertFailure
            $  "Unexpected success parsing `"
            ++ file
            ++ ":\nParsed value: "
            ++ show expr
        Failure _ -> pure ()
      )
    $ \(_ :: SomeException) -> pure ()

assertLangOk :: Options -> FilePath -> Assertion
assertLangOk opts file = do
  actual   <- printNix <$> hnixEvalFile opts (file ++ ".nix")
  expected <- Text.readFile $ file ++ ".exp"
  assertEqual "" expected $ Text.pack (actual ++ "\n")

assertLangOkXml :: Options -> FilePath -> Assertion
assertLangOkXml opts file = do
  actual <- stringIgnoreContext . toXML <$> hnixEvalFile
    opts
    (file ++ ".nix")
  expected <- Text.readFile $ file ++ ".exp.xml"
  assertEqual "" expected actual

assertEval :: Options -> [FilePath] -> Assertion
assertEval _opts files = do
  time <- liftIO getCurrentTime
  let opts = defaultOptions time
  case delete ".nix" $ sort $ map takeExtensions files of
    []                 -> () <$ hnixEvalFile opts (name ++ ".nix")
    [".exp"         ]  -> assertLangOk opts name
    [".exp.xml"     ]  -> assertLangOkXml opts name
    [".exp.disabled"]  -> pure ()
    [".exp-disabled"]  -> pure ()
    [".exp", ".flags"] -> do
      liftIO $ setEnv "NIX_PATH" "lang/dir4:lang/dir5"
      flags <- Text.readFile (name ++ ".flags")
      let flags' | Text.last flags == '\n' = Text.init flags
                 | otherwise               = flags
      case
          Opts.execParserPure
            Opts.defaultPrefs
            (nixOptionsInfo time)
            (fixup (map Text.unpack (Text.splitOn " " flags')))
        of
          Opts.Failure err ->
            errorWithoutStackTrace
              $  "Error parsing flags from "
              ++ name
              ++ ".flags: "
              ++ show err
          Opts.Success opts' -> assertLangOk opts' name
          Opts.CompletionInvoked _ -> error "unused"
    _ -> assertFailure $ "Unknown test type " ++ show files
 where
  name =
    "data/nix/tests/lang/" ++ the (map (takeFileName . dropExtensions) files)

  fixup ("--arg"    : x : y : rest) = "--arg" : (x ++ "=" ++ y) : fixup rest
  fixup ("--argstr" : x : y : rest) = "--argstr" : (x ++ "=" ++ y) : fixup rest
  fixup (x                  : rest) = x : fixup rest
  fixup []                          = []

assertEvalFail :: FilePath -> Assertion
assertEvalFail file = catch ?? (\(_ :: SomeException) -> pure ()) $ do
  time       <- liftIO getCurrentTime
  evalResult <- printNix <$> hnixEvalFile (defaultOptions time) file
  evalResult
    `seq` assertFailure
    $     file
    ++    " should not evaluate.\nThe evaluation result was `"
    ++    evalResult
    ++    "`."
