{- This code was authored by:

     Stephen Diehl
     Kwang Yul Seo <kwangyul.seo@gmail.com>

   It was made available under the MIT license. See the src/Nix/Type
   directory for more details.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Repl
  ( main
  , main'
  ) where

import           Nix                     hiding ( exec
                                                , try
                                                )
import           Nix.Scope
import           Nix.Utils
import           Nix.Value.Monad                (demand)

import qualified Data.List
import qualified Data.Maybe
import qualified Data.HashMap.Lazy
import           Data.Interned
import           Data.Text                      (Text)
import qualified Data.Text
import qualified Data.Text.IO
import           Data.Version                   ( showVersion )
import           Paths_hnix                     ( version )

import           Control.Arrow                  ( first )
import           Control.Monad.Catch
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.State.Strict

import           Prettyprinter                  (Doc, (<+>))
import qualified Prettyprinter
import qualified Prettyprinter.Render.Text

import           System.Console.Haskeline.Completion
                                                ( Completion(isFinished)
                                                , completeWordWithPrev
                                                , simpleCompletion
                                                , listFiles
                                                )
import           System.Console.Repline         ( Cmd
                                                , CompletionFunc
                                                , CompleterStyle (Prefix)
                                                , ExitDecision(Exit)
                                                , HaskelineT
                                                )
import qualified System.Console.Repline
import qualified System.Exit
import qualified System.IO.Error

-- | Repl entry point
main :: (MonadNix e t f m, MonadIO m, MonadMask m) =>  m ()
main = main' Nothing

-- | Principled version allowing to pass initial value for context.
--
-- Passed value is stored in context with "input" key.
main' :: (MonadNix e t f m, MonadIO m, MonadMask m) => Maybe (NValue t f m) -> m ()
main' iniVal = initState iniVal >>= \s -> flip evalStateT s
    $ System.Console.Repline.evalRepl
        banner
        cmd
        options
        (Just commandPrefix)
        (Just "paste")
        completion
        (rcFile >> greeter)
        finalizer
 where
  commandPrefix = ':'

  banner = pure . \case
    System.Console.Repline.SingleLine -> "hnix> "
    System.Console.Repline.MultiLine  -> "| "

  greeter =
    liftIO
      $  putStrLn
      $  "Welcome to hnix "
      <> showVersion version
      <> ". For help type :help\n"
  finalizer = do
    liftIO $ putStrLn "Goodbye."
    pure Exit

  rcFile = do
    f <- liftIO $ Data.Text.IO.readFile ".hnixrc" `catch` handleMissing
    forM_ (map (words . Data.Text.unpack) $ Data.Text.lines f) $ \case
      ((prefix:command) : xs) | prefix == commandPrefix -> do
        let arguments = unwords xs
        optMatcher command options arguments
      x -> cmd $ unwords x

  handleMissing e
    | System.IO.Error.isDoesNotExistError e = pure ""
    | otherwise = throwIO e

  -- Replicated and slightly adjusted `optMatcher` from `System.Console.Repline`
  -- which doesn't export it.
  -- * @MonadIO m@ instead of @MonadHaskeline m@
  -- * @putStrLn@ instead of @outputStrLn@
  optMatcher :: MonadIO m
             => String
             -> System.Console.Repline.Options m
             -> String
             -> m ()
  optMatcher s [] _ = liftIO $ putStrLn $ "No such command :" ++ s
  optMatcher s ((x, m) : xs) args
    | s `Data.List.isPrefixOf` x = m args
    | otherwise = optMatcher s xs args

---------------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------------

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

  pure $ IState
    Nothing
    (Data.HashMap.Lazy.fromList
      $ ("builtins", builtins) : fmap ("input",) (Data.Maybe.maybeToList mIni))
    defReplConfig
      { cfgStrict = strict opts
      , cfgValues = values opts
      }
  where
    evalText :: (MonadNix e t f m) => Text -> m (NValue t f m)
    evalText expr = case parseNixTextLoc expr of
      Failure e -> error $ "Impossible happened: Unable to parse expression - '" ++ Data.Text.unpack expr ++ "' error was " ++ show e
      Success e -> do evalExprLoc e

type Repl e t f m = HaskelineT (StateT (IState t f m) m)

---------------------------------------------------------------------------------
-- * Execution
---------------------------------------------------------------------------------

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
    (Failure err, _) -> do
      liftIO $ print err
      pure Nothing
    (Success expr, isBinding) -> do

      -- Type Inference ( returns Typing Environment )
      --
      -- import qualified Nix.Type.Env                  as Env
      -- import           Nix.Type.Infer
      --
      -- let tyctx' = inferTop Env.empty [("repl", stripAnnotation expr)]
      -- liftIO $ print tyctx'

      mVal <- lift $ lift $ try $ pushScope (replCtx st) (evalExprLoc expr)

      case mVal of
        Left (NixException frames) -> do
          lift $ lift $ liftIO . print =<< renderFrames @(NValue t f m) @t frames
          pure Nothing
        Right val -> do
          -- Update the interpreter state
          when (update && isBinding) $ do
            -- Set `replIt` to last entered expression
            put st { replIt = Just expr }

            -- If the result value is a set, update our context with it
            case val of
              NVSet xs _ -> put st { replCtx = Data.HashMap.Lazy.union xs (replCtx st) }
              _          -> pure ()

          pure $ Just val
  where
    -- If parsing fails, turn the input into singleton attribute set
    -- and try again.
    --
    -- This allows us to handle assignments like @a = 42@
    -- which get turned into @{ a = 42; }@
    parseExprOrBinding i =
      case parseNixTextLoc i of
        Success expr -> (Success expr, False)
        Failure e    ->
          case parseNixTextLoc $ toAttrSet i of
            Failure _  -> (Failure e, False) -- return the first parsing failure
            Success e' -> (Success e', True)

    toAttrSet i = "{" <> i <> (if Data.Text.isSuffixOf ";" i then mempty else ";") <> "}"

cmd
  :: (MonadNix e t f m, MonadIO m)
  => String
  -> Repl e t f m ()
cmd source = do
  mVal <- exec True (Data.Text.pack source)
  case mVal of
    Nothing -> pure ()
    Just val -> printValue val

printValue :: (MonadNix e t f m, MonadIO m)
           => NValue t f m
           -> Repl e t f m ()
printValue val = do
  cfg <- replCfg <$> get
  lift $ lift $ do
    if
      | cfgStrict cfg -> liftIO . print . prettyNValue =<< normalForm val
      | cfgValues cfg -> liftIO . print . prettyNValueProv =<< removeEffects val
      | otherwise     -> liftIO . print . prettyNValue =<< removeEffects val

---------------------------------------------------------------------------------
-- * Commands
---------------------------------------------------------------------------------

-- :browse command
browse :: (MonadNix e t f m, MonadIO m)
       => String
       -> Repl e t f m ()
browse _ = do
  st <- get
  forM_ (Data.HashMap.Lazy.toList $ replCtx st) $ \(k, v) -> do
    liftIO $ putStr $ Data.Text.unpack $ unintern k <> " = "
    printValue v

-- :load command
load
  :: (MonadNix e t f m, MonadIO m)
  => String
  -> Repl e t f m ()
load args = do
  contents <- liftIO
    $ Data.Text.IO.readFile
    $ Data.Text.unpack
    $ Data.Text.strip
    $ Data.Text.pack args
  void $ exec True contents

-- :type command
typeof
  :: (MonadNix e t f m, MonadIO m)
  => String
  -> Repl e t f m ()
typeof args = do
  st <- get
  mVal <- case Data.HashMap.Lazy.lookup (intern line) (replCtx st) of
    Just val -> pure $ Just val
    Nothing  -> do
      exec False line

  forM_ mVal $ \val -> do
    s <- lift . lift . showValueType $ val
    liftIO $ putStrLn s

  where line = Data.Text.pack args

-- :quit command
quit :: (MonadNix e t f m, MonadIO m) => a -> Repl e t f m ()
quit _ = liftIO System.Exit.exitSuccess

-- :set command
setConfig :: (MonadNix e t f m, MonadIO m) => String -> Repl e t f m ()
setConfig args = case words args of
  []       -> liftIO $ putStrLn "No option to set specified"
  (x:_xs)  ->
    case filter ((==x) . helpSetOptionName) helpSetOptions of
      [opt] -> modify (\s -> s { replCfg = helpSetOptionFunction opt (replCfg s) })
      _     -> liftIO $ putStrLn "No such option"

---------------------------------------------------------------------------------
-- * Interactive Shell
---------------------------------------------------------------------------------

-- Prefix tab completer
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher =
  [ (":load", System.Console.Repline.fileCompleter)
  ]

completion
  :: (MonadNix e t f m, MonadIO m)
  => CompleterStyle (StateT (IState t f m) m)
completion = System.Console.Repline.Prefix
  (completeWordWithPrev (Just '\\') separators completeFunc)
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
  => String
  -> String
  -> (StateT (IState t f m) m) [Completion]
completeFunc reversedPrev word
  -- Commands
  | reversedPrev == ":"
  = pure . listCompletion
      $ map helpOptionName (helpOptions :: HelpOptions e t f m)

  -- Files
  | any (`Data.List.isPrefixOf` word) [ "/", "./", "../", "~/" ]
  = listFiles word

  -- Attributes of sets in REPL context
  | var : subFields <- Data.Text.split (== '.') (Data.Text.pack word)
  , not $ null subFields
  = do
    s <- get
    case Data.HashMap.Lazy.lookup (intern var) (replCtx s) of
      Nothing -> pure []
      Just binding -> do
        candidates <- lift $ algebraicComplete subFields binding
        pure
          $ map notFinished
          $ listCompletion (Data.Text.unpack . (var <>) <$> candidates)

  -- Builtins, context variables
  | otherwise
  = do
    s <- get
    let contextKeys = Data.HashMap.Lazy.keys (replCtx s)
        (Just (NVSet builtins _)) = Data.HashMap.Lazy.lookup "builtins" (replCtx s)
        shortBuiltins = Data.HashMap.Lazy.keys builtins

    pure $ listCompletion
      $ ["__includes"]
      ++ (Data.Text.unpack . unintern <$> contextKeys)
      ++ (Data.Text.unpack . unintern <$> shortBuiltins)

  where
    listCompletion = map simpleCompletion . filter (word `Data.List.isPrefixOf`)

    notFinished x = x { isFinished = False }

    algebraicComplete :: (MonadNix e t f m)
                      => [Text]
                      -> NValue t f m
                      -> m [Text]
    algebraicComplete subFields val =
      let keys = map (\k -> "." <> (unintern k)) . Data.HashMap.Lazy.keys
          withMap m =
            case subFields of
              [] -> pure $ keys m
              -- Stop on last subField (we care about the keys at this level)
              [_] -> pure $ keys m
              f:fs ->
                case Data.HashMap.Lazy.lookup (intern f) m of
                  Nothing -> pure []
                  Just e ->
                    demand e
                    (\e' -> fmap (("." <> f) <>) <$> algebraicComplete fs e')

      in case val of
        NVSet xs _ -> withMap xs
        _          -> pure []

-- HelpOption inspired by Dhall Repl
-- with `Doc` instead of String for syntax and doc
data HelpOption e t f m = HelpOption
  { helpOptionName     :: String
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
      (help helpOptions)
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
      browse
  , HelpOption
      "type"
      "EXPRESSION"
      "Evaluate expression or binding from context and print the type of the result value"
      typeof
  , HelpOption
      "quit"
      ""
      "Quit interpreter"
      quit
  , HelpOption
      "set"
      ""
      (    "Set REPL option"
        <> Prettyprinter.line
        <> "Available options:"
        <> Prettyprinter.line
        <> renderSetOptions helpSetOptions
      )
      setConfig
  ]

-- Options for :set
data HelpSetOption = HelpSetOption
  { helpSetOptionName     :: String
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
  Prettyprinter.indent 4
    $ Prettyprinter.vsep
    $ flip map so
    $ \h ->
             Prettyprinter.pretty (helpSetOptionName h)
         <+> helpSetOptionSyntax h
         <>  Prettyprinter.line
         <>  Prettyprinter.indent 4 (helpSetOptionDoc h)

help :: (MonadNix e t f m, MonadIO m)
     => HelpOptions e t f m
     -> String
     -> Repl e t f m ()
help hs _ = do
  liftIO $ putStrLn "Available commands:\n"
  forM_ hs $ \h ->
      liftIO
    . Data.Text.IO.putStrLn
    . Prettyprinter.Render.Text.renderStrict
    . Prettyprinter.layoutPretty
        Prettyprinter.defaultLayoutOptions
    $     ":"
       <>  Prettyprinter.pretty (helpOptionName h)
       <+> helpOptionSyntax h
       <>  Prettyprinter.line
       <>  Prettyprinter.indent 4 (helpOptionDoc h)

options
  :: (MonadNix e t f m, MonadIO m)
  => System.Console.Repline.Options (Repl e t f m)
options = (\h -> (helpOptionName h, helpOptionFunction h)) <$> helpOptions
