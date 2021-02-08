{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Nix
  ( module Nix.Cache
  , module Nix.Exec
  , module Nix.Expr
  , module Nix.Frames
  , module Nix.Render.Frame
  , module Nix.Normal
  , module Nix.Options
  , module Nix.String
  , module Nix.Parser
  , module Nix.Pretty
  , module Nix.Reduce
  , module Nix.Thunk
  , module Nix.Value
  , module Nix.XML
  , withNixContext
  , nixEvalExpr
  , nixEvalExprLoc
  , nixTracingEvalExprLoc
  , evaluateExpression
  , processResult
  )
where

import           Control.Applicative
import           Control.Arrow                  ( second )
import           Control.Monad.Reader
import           Data.Fix
import qualified Data.HashMap.Lazy             as M
import qualified Data.Text                     as Text
import qualified Data.Text.Read                as Text
import           Nix.Builtins
import           Nix.Cache
import qualified Nix.Eval                      as Eval
import           Nix.Exec
import           Nix.Expr
import           Nix.Frames
import           Nix.String
import           Nix.Normal
import           Nix.Options
import           Nix.Parser
import           Nix.Pretty
import           Nix.Reduce
import           Nix.Render.Frame
import           Nix.Thunk
import           Nix.Utils
import           Nix.Value
import           Nix.Value.Monad
import           Nix.XML

-- | This is the entry point for all evaluations, whatever the expression tree
--   type. It sets up the common Nix environment and applies the
--   transformations, allowing them to be easily composed.
nixEval
  :: (MonadNix e f m, Has e Options, Functor g)
  => Maybe FilePath
  -> Transform g (m a)
  -> Alg g (m a)
  -> Fix g
  -> m a
nixEval mpath xform alg = withNixContext mpath . adi alg xform

-- | Evaluate a nix expression in the default context
nixEvalExpr
  :: forall e f m.
     (MonadNix e f m, Has e Options)
  => Maybe FilePath
  -> NExpr
  -> m (NValue f m)
nixEvalExpr mpath = nixEval mpath id Eval.eval

-- | Evaluate a nix expression in the default context
nixEvalExprLoc
  :: forall e f m
   . (MonadNix e f m, Has e Options)
  => Maybe FilePath
  -> NExprLoc
  -> m (NValue f m)
nixEvalExprLoc mpath = nixEval
  mpath
  (Eval.addStackFrames . Eval.addSourcePositions)
  (Eval.eval . annotated . getCompose)

-- | Evaluate a nix expression with tracing in the default context. Note that
--   this function doesn't do any tracing itself, but 'evalExprLoc' will be
--   'tracing' is set to 'True' in the Options structure (accessible through
--   'MonadNix'). All this function does is provide the right type class
--   context.
nixTracingEvalExprLoc
  :: (MonadNix e f m, Has e Options, MonadIO m, Alternative m)
  => Maybe FilePath
  -> NExprLoc
  -> m (NValue f m)
nixTracingEvalExprLoc mpath = withNixContext mpath . evalExprLoc

evaluateExpression
  :: (MonadNix e f m, Has e Options)
  => Maybe FilePath
  -> (Maybe FilePath -> NExprLoc -> m (NValue f m))
  -> (NValue f m -> m a)
  -> NExprLoc
  -> m a
evaluateExpression mpath evaluator handler expr = do
  opts :: Options <- asks (view hasLens)
  args <- traverse (traverse eval') $ fmap (second parseArg) (arg opts) ++ fmap
    (second mkStr)
    (argstr opts)
  evaluator mpath expr >>= \f -> demand f $ \f' ->
    processResult handler =<< case f' of
      NVClosure _ g -> g (argmap args)
      _             -> pure f
 where
  parseArg s = case parseNixText s of
    Success x   -> x
    Failure err -> errorWithoutStackTrace (show err)

  eval' = normalForm <=< nixEvalExpr mpath

  argmap args = nvSet (M.fromList args) mempty

processResult
  :: forall e f m a
   . (MonadNix e f m, Has e Options)
  => (NValue f m -> m a)
  -> NValue f m
  -> m a
processResult h val = do
  opts :: Options <- asks (view hasLens)
  case attr opts of
    Nothing                         -> h val
    Just (Text.splitOn "." -> keys) -> go keys val
 where
  go :: [Text.Text] -> NValue f m -> m a
  go [] v = h v
  go ((Text.decimal -> Right (n,"")) : ks) v = demand v $ \case
    NVList xs -> case ks of
      [] -> h (xs !! n)
      _  -> go ks (xs !! n)
    _ ->
      errorWithoutStackTrace
        $  "Expected a list for selector '"
        ++ show n
        ++ "', but got: "
        ++ show v
  go (k : ks) v = demand v $ \case
    NVSet xs _ -> case M.lookup k xs of
      Nothing ->
        errorWithoutStackTrace
          $  "Set does not contain key '"
          ++ Text.unpack k
          ++ "'"
      Just v' -> case ks of
        [] -> h v'
        _  -> go ks v'
    _ ->
      errorWithoutStackTrace
        $  "Expected a set for selector '"
        ++ Text.unpack k
        ++ "', but got: "
        ++ show v
