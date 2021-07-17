{- This code was authored by:

     Stephen Diehl
     Kwang Yul Seo <kwangyul.seo@gmail.com>

   It was made available under the MIT license. See the src/Nix/Type
   directory for more details.
-}

{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Repl
  ( main
  , main'
  ) where

import           Nix                     hiding ( exec
                                                , try
                                                )
import           Nix.Scope
import           Nix.Utils
import           Nix.Value.Monad                ( demand )

import qualified Data.HashMap.Lazy
import           Data.Char                      ( isSpace )
import           Data.List                      ( dropWhileEnd )
import qualified Data.Text                   as Text
import qualified Data.Text.IO                as Text
import           Data.Version                   ( showVersion )
import           Paths_hnix                     ( version )

import           Control.Monad.Catch

import           Prettyprinter                  ( Doc
                                                , space
                                                )
import qualified Prettyprinter
import qualified Prettyprinter.Render.Text    as Prettyprinter

import           System.Console.Haskeline.Completion
                                                ( Completion(isFinished)
                                                , completeWordWithPrev
                                                , simpleCompletion
                                                , listFiles
                                                )
import           System.Console.Repline         ( Cmd
                                                , CompletionFunc
                                                , CompleterStyle(Prefix)
                                                , MultiLine(SingleLine, MultiLine)
                                                , ExitDecision(Exit)
                                                , HaskelineT
                                                , evalRepl
                                                )
import qualified System.Console.Repline      as Console
import qualified System.Exit                 as Exit
import qualified System.IO.Error             as Error

-- | Repl entry point
main :: (MonadNix e t f m, MonadIO m, MonadMask m) =>  m ()
main = main' Nothing

-- | Principled version allowing to pass initial value for context.
--
-- Passed value is stored in context with "input" key.
main' :: (MonadNix e t f m, MonadIO m, MonadMask m) => Maybe (NValue t f m) -> m ()
main' iniVal =
  do
    s <- initState iniVal

    evalStateT
      (evalRepl
        banner
        (cmd . toText)
        options
        (pure commandPrefix)
        (pure "paste")
        completion
        (rcFile *> greeter)
        finalizer
      )
      s
 where
  commandPrefix = ':'

  banner = pure . \case
    SingleLine -> "hnix> "
    MultiLine  -> "| "

  greeter =
    liftIO $
      putStrLn $
        "Welcome to hnix "
        <> showVersion version
        <> ". For help type :help\n"
  finalizer = do
    liftIO $ putStrLn "Goodbye."
    pure Exit

  rcFile =
    do
      f <- liftIO $ Text.readFile ".hnixrc" `catch` handleMissing

      traverse_
        (\case
          (prefixedCommand : xs) | Text.head prefixedCommand == commandPrefix ->
            do
              let
                arguments = unwords xs
                command = Text.tail prefixedCommand
              optMatcher command options arguments
          x -> cmd $ unwords x
        )
        (words <$> lines f)

  handleMissing e
    | Error.isDoesNotExistError e = pure ""
    | otherwise = throwIO e

  -- Replicated and slightly adjusted `optMatcher` from `System.Console.Repline`
  -- which doesn't export it.
  -- * @MonadIO m@ instead of @MonadHaskeline m@
  -- * @putStrLn@ instead of @outputStrLn@
  optMatcher :: MonadIO m
             => Text
             -> Console.Options m
             -> Text
             -> m ()
  optMatcher s [] _ = liftIO $ Text.putStrLn $ "No such command :" <> s
  optMatcher s ((x, m) : xs) args
    | s `Text.isPrefixOf` toText x = m $ toString args
    | otherwise = optMatcher s xs args


-- * Types

data IState t f m = IState
  { replIt  :: Maybe NExprLoc          -- ^ Last expression entered
  , replCtx :: AttrSet (NValue t f m)  -- ^ Value environment
  , replCfg :: ReplConfig              -- ^ REPL configuration
  } deriving (Eq, Show)

data ReplConfig = ReplConfig
  { cfgDebug  :: Bool
  , cfgStrict :: Bool
  , cfgValues :: Bool
  } deriving (Eq, Show)

defReplConfig :: ReplConfig
defReplConfig = ReplConfig
  { cfgDebug  = False
  , cfgStrict = False
  , cfgValues = False
  }

-- | Create initial IState for REPL
initState :: MonadNix e t f m => Maybe (NValue t f m) -> m (IState t f m)
initState mIni = do

  builtins <- evalText "builtins"

  opts :: Nix.Options <- asks (view hasLens)

  pure $
    IState
      Nothing
      (Data.HashMap.Lazy.fromList $
        ("builtins", builtins) : fmap ("input",) (maybeToList mIni)
      )
      defReplConfig
        { cfgStrict = strict opts
        , cfgValues = values opts
        }
  where
    evalText :: (MonadNix e t f m) => Text -> m (NValue t f m)
    evalText expr =
      either
        (\ e -> fail $ toString $ "Impossible happened: Unable to parse expression - '" <> expr <> "' fail was " <> show e)
        evalExprLoc
        (parseNixTextLoc expr)

type Repl e t f m = HaskelineT (StateT (IState t f m) m)


-- * Execution

exec
  :: forall e t f m
   . (MonadNix e t f m, MonadIO m)
  => Bool
  -> Text
  -> Repl e t f m (Maybe (NValue t f m))
exec update source = do
  -- Get the current interpreter state
  st <- get

  when (cfgDebug $ replCfg st) $ liftIO $ print st

  -- Parser ( returns AST as `NExprLoc` )
  case parseExprOrBinding source of
    (Left err, _) -> do
      liftIO $ print err
      pure Nothing
    (Right expr, isBinding) -> do

      -- Type Inference ( returns Typing Environment )
      --
      -- import qualified Nix.Type.Env                  as Env
      -- import           Nix.Type.Infer
      --
      -- let tyctx' = inferTop mempty [("repl", stripAnnotation expr)]
      -- liftIO $ print tyctx'

      mVal <- lift $ lift $ try $ pushScope (replCtx st) (evalExprLoc expr)

      either
        (\ (NixException frames) -> do
          lift $ lift $ liftIO . print =<< renderFrames @(NValue t f m) @t frames
          pure Nothing)
        (\ val -> do
          -- Update the interpreter state
          when (update && isBinding) $ do
            -- Set `replIt` to last entered expression
            put st { replIt = pure expr }

            -- If the result value is a set, update our context with it
            case val of
              NVSet _ xs -> put st { replCtx = xs <> replCtx st }
              _          -> pass

          pure $ pure val
        )
        mVal
  where
    -- If parsing fails, turn the input into singleton attribute set
    -- and try again.
    --
    -- This allows us to handle assignments like @a = 42@
    -- which get turned into @{ a = 42; }@
    parseExprOrBinding i =
      either
        (\ e    ->
          either
            (const (Left e, False)) -- return the first parsing failure
            (\ e' -> (pure e', True))
            (parseNixTextLoc $ toAttrSet i))
        (\ expr -> (pure expr, False))
        (parseNixTextLoc i)

    toAttrSet i =
      "{" <> i <> bool ";" mempty (Text.isSuffixOf ";" i) <> "}"

cmd
  :: (MonadNix e t f m, MonadIO m)
  => Text
  -> Repl e t f m ()
cmd source =
  do
    mVal <- exec True source
    maybe
      pass
      printValue
      mVal

printValue :: (MonadNix e t f m, MonadIO m)
           => NValue t f m
           -> Repl e t f m ()
printValue val = do
  cfg <- replCfg <$> get
  lift $ lift $
    (if
      | cfgStrict cfg -> liftIO . print . prettyNValue     <=< normalForm
      | cfgValues cfg -> liftIO . print . prettyNValueProv <=< removeEffects
      | otherwise     -> liftIO . print . prettyNValue     <=< removeEffects
    ) val


-- * Commands

-- | @:browse@ command
browse :: (MonadNix e t f m, MonadIO m)
       => Text
       -> Repl e t f m ()
browse _ =
  do
    st <- get
    traverse_
      (\(k, v) ->
        do
          liftIO $ Text.putStr $ coerce k <> " = "
          printValue v
      )
      (Data.HashMap.Lazy.toList $ replCtx st)

-- | @:load@ command
load
  :: (MonadNix e t f m, MonadIO m)
  -- This one does I String -> O String pretty fast, it is ugly to double marshall here.
  => String
  -> Repl e t f m ()
load args =
  do
    contents <- liftIO $
      Text.readFile $
       trim args
    void $ exec True contents
 where
  trim = dropWhileEnd isSpace . dropWhile isSpace

-- | @:type@ command
typeof
  :: (MonadNix e t f m, MonadIO m)
  => Text
  -> Repl e t f m ()
typeof args = do
  st <- get
  mVal <-
    maybe
      (exec False line)
      (pure . pure)
      (Data.HashMap.Lazy.lookup (coerce line) (replCtx st))

  traverse_ printValueType mVal

 where
  line = args
  printValueType val =
    do
      s <- lift . lift . showValueType $ val
      liftIO $ Text.putStrLn s


-- | @:quit@ command
quit :: (MonadNix e t f m, MonadIO m) => a -> Repl e t f m ()
quit _ = liftIO Exit.exitSuccess

-- | @:set@ command
setConfig :: (MonadNix e t f m, MonadIO m) => Text -> Repl e t f m ()
setConfig args =
  list
    (liftIO $ Text.putStrLn "No option to set specified")
    (\ (x:_xs)  ->
      case filter ((==x) . helpSetOptionName) helpSetOptions of
        [opt] -> modify (\s -> s { replCfg = helpSetOptionFunction opt (replCfg s) })
        _     -> liftIO $ Text.putStrLn "No such option"
    )
    $ words args


-- * Interactive Shell

-- | Prefix tab completer
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher =
  [ (":load", Console.fileCompleter)
  ]

completion
  :: (MonadNix e t f m, MonadIO m)
  => CompleterStyle (StateT (IState t f m) m)
completion = System.Console.Repline.Prefix
  (completeWordWithPrev (pure '\\') separators completeFunc)
  defaultMatcher
  where
    separators :: String
    separators = " \t[(,=+*&|}#?>:"

-- | Main completion function
--
-- Heavily inspired by Dhall Repl, with `algebraicComplete`
-- adjusted to monadic variant able to `demand` thunks.
completeFunc
  :: forall e t f m . (MonadNix e t f m, MonadIO m)
  -- 2021-04-02: So far conversiton to Text here is not productive,
  -- since Haskeline uses String of all this.
  => String
  -> String
  -> (StateT (IState t f m) m) [Completion]
completeFunc reversedPrev word
  -- Commands
  | reversedPrev == ":" =
    pure . listCompletion $
      toString . helpOptionName <$>
        (helpOptions :: HelpOptions e t f m)

  -- Files
  | any (`isPrefixOf` word) [ "/", "./", "../", "~/" ] =
    listFiles word

  -- Attributes of sets in REPL context
  | var : subFields <- Text.split (== '.') (toText word) , not $ null subFields =
    do
      s <- get
      maybe
        stub
        (\ binding ->
          do
            candidates <- lift $ algebraicComplete subFields binding
            pure $
              notFinished <$>
                listCompletion
                  (toString . (var <>) <$>
                    candidates
                  )
        )
        (Data.HashMap.Lazy.lookup (coerce var) (replCtx s))

  -- Builtins, context variables
  | otherwise =
    do
      s <- get
      let contextKeys = Data.HashMap.Lazy.keys (replCtx s)
          (Just (NVSet _ builtins)) = Data.HashMap.Lazy.lookup "builtins" (replCtx s)
          shortBuiltins = Data.HashMap.Lazy.keys builtins

      pure $ listCompletion $ toString <$>
        ["__includes"]
          <> contextKeys
          <> shortBuiltins

  where
    listCompletion = fmap simpleCompletion . filter (word `isPrefixOf`)

    notFinished x = x { isFinished = False }

    algebraicComplete
      :: (MonadNix e t f m)
      => [Text]
      -> NValue t f m
      -> m [Text]
    algebraicComplete subFields val =
      let
        keys = fmap ("." <>) . Data.HashMap.Lazy.keys

        withMap m =
          case subFields of
            [] -> pure $ keys m
            -- Stop on last subField (we care about the keys at this level)
            [_] -> pure $ keys m
            f:fs ->
              maybe
                stub
                ((<<$>>)
                   (("." <> f) <>)
                   . algebraicComplete fs <=< demand
                )
                (Data.HashMap.Lazy.lookup (coerce f) m)
      in
      case val of
        NVSet _ xs -> withMap (Data.HashMap.Lazy.mapKeys coerce xs)
        _          -> stub

-- | HelpOption inspired by Dhall Repl
-- with `Doc` instead of String for syntax and doc
data HelpOption e t f m = HelpOption
  { helpOptionName     :: Text
  , helpOptionSyntax   :: Doc ()
  , helpOptionDoc      :: Doc ()
  , helpOptionFunction :: Cmd (Repl e t f m)
  }

type HelpOptions e t f m = [HelpOption e t f m]

helpOptions :: (MonadNix e t f m, MonadIO m) => HelpOptions e t f m
helpOptions =
  [ HelpOption
      "help"
      ""
      "Print help text"
      (help helpOptions . toText)
  , HelpOption
      "paste"
      ""
      "Enter multi-line mode"
      (error "Unreachable")
  , HelpOption
      "load"
      "FILENAME"
      "Load .nix file into scope"
      load
  , HelpOption
      "browse"
      ""
      "Browse bindings in interpreter context"
      (browse . toText)
  , HelpOption
      "type"
      "EXPRESSION"
      "Evaluate expression or binding from context and print the type of the result value"
      (typeof . toText)
  , HelpOption
      "quit"
      ""
      "Quit interpreter"
      quit
  , HelpOption
      "set"
      ""
      ("Set REPL option"
        <> Prettyprinter.line
        <> "Available options:"
        <> Prettyprinter.line
        <> renderSetOptions helpSetOptions
      )
      (setConfig . toText)
  ]

-- | Options for :set
data HelpSetOption = HelpSetOption
  { helpSetOptionName     :: Text
  , helpSetOptionSyntax   :: Doc ()
  , helpSetOptionDoc      :: Doc ()
  , helpSetOptionFunction :: ReplConfig -> ReplConfig
  }

helpSetOptions :: [HelpSetOption]
helpSetOptions =
  [ HelpSetOption
      "strict"
      ""
      "Enable strict evaluation of REPL expressions"
      (\x -> x { cfgStrict = True})
  , HelpSetOption
      "lazy"
      ""
      "Disable strict evaluation of REPL expressions"
      (\x -> x { cfgStrict = False})
  , HelpSetOption
      "values"
      ""
      "Enable printing of value provenance information"
      (\x -> x { cfgValues = True})
  , HelpSetOption
      "novalues"
      ""
      "Disable printing of value provenance information"
      (\x -> x { cfgValues = False})
  , HelpSetOption
      "debug"
      ""
      "Enable printing of REPL debug information"
      (\x -> x { cfgDebug = True})
  , HelpSetOption
      "nodebug"
      ""
      "Disable REPL debugging"
      (\x -> x { cfgDebug = False})
  ]

renderSetOptions :: [HelpSetOption] -> Doc ()
renderSetOptions so =
  Prettyprinter.indent 4 $
    Prettyprinter.vsep $
      (\h ->
        Prettyprinter.pretty (helpSetOptionName h) <> space
        <> helpSetOptionSyntax h
        <> Prettyprinter.line
        <> Prettyprinter.indent 4 (helpSetOptionDoc h)
      ) <$> so

help :: (MonadNix e t f m, MonadIO m)
     => HelpOptions e t f m
     -> Text
     -> Repl e t f m ()
help hs _ = do
  liftIO $ putStrLn "Available commands:\n"
  for_ hs $ \h ->
    liftIO .
      Text.putStrLn .
        Prettyprinter.renderStrict .
          Prettyprinter.layoutPretty Prettyprinter.defaultLayoutOptions $
            ":"
            <> Prettyprinter.pretty (helpOptionName h) <> space
            <> helpOptionSyntax h
            <> Prettyprinter.line
            <> Prettyprinter.indent 4 (helpOptionDoc h)

options
  :: (MonadNix e t f m, MonadIO m)
  => Console.Options (Repl e t f m)
options = (\h -> (toString $ helpOptionName h, helpOptionFunction h)) <$> helpOptions
