{-# LANGUAGE ScopedTypeVariables #-}
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

import           Relude.Unsafe                  ( (!!) )
import           GHC.Err                        ( errorWithoutStackTrace )
import           Data.Fix                       ( Fix )
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
  :: (MonadNix e t f m, Has e Options, Functor g)
  => Transform g (m a)
  -> Alg g (m a)
  -> Maybe FilePath
  -> Fix g
  -> m a
nixEval transform alg mpath = withNixContext mpath . adi transform alg

-- | Evaluate a nix expression in the default context
nixEvalExpr
  :: (MonadNix e t f m, Has e Options)
  => Maybe FilePath
  -> NExpr
  -> m (NValue t f m)
nixEvalExpr = nixEval id Eval.eval

-- | Evaluate a nix expression in the default context
nixEvalExprLoc
  :: forall e t f m
   . (MonadNix e t f m, Has e Options)
  => Maybe FilePath
  -> NExprLoc
  -> m (NValue t f m)
nixEvalExprLoc =
  nixEval
    Eval.addMetaInfo
    Eval.evalContent

-- | Evaluate a nix expression with tracing in the default context. Note that
--   this function doesn't do any tracing itself, but 'evalExprLoc' will be
--   'tracing' is set to 'True' in the Options structure (accessible through
--   'MonadNix'). All this function does is provide the right type class
--   context.
nixTracingEvalExprLoc
  :: (MonadNix e t f m, Has e Options, MonadIO m, Alternative m)
  => Maybe FilePath
  -> NExprLoc
  -> m (NValue t f m)
nixTracingEvalExprLoc mpath = withNixContext mpath . evalExprLoc

evaluateExpression
  :: (MonadNix e t f m, Has e Options)
  => Maybe FilePath
  -> (Maybe FilePath -> NExprLoc -> m (NValue t f m))
  -> (NValue t f m -> m a)
  -> NExprLoc
  -> m a
evaluateExpression mpath evaluator handler expr =
  do
    opts :: Options <- asks $ view hasLens
    (coerce -> args) <-
      (traverse . traverse)
        eval'
        $  (second parseArg <$> arg    opts)
        <> (second mkStr    <$> argstr opts)
    f <- evaluator mpath expr
    f' <- demand f
    val <-
      case f' of
        NVClosure _ g -> g $ argmap args
        _             -> pure f
    processResult handler val
 where
  parseArg s =
    either
      (errorWithoutStackTrace . show)
      id
      (parseNixText s)

  eval' = normalForm <=< nixEvalExpr mpath

  argmap args = nvSet mempty $ M.fromList args

processResult
  :: forall e t f m a
   . (MonadNix e t f m, Has e Options)
  => (NValue t f m -> m a)
  -> NValue t f m
  -> m a
processResult h val = do
  opts :: Options <- asks $ view hasLens
  maybe
    (h val)
    (\ (coerce . Text.splitOn "." -> keys) -> processKeys keys val)
    (attr opts)
 where
  processKeys :: [VarName] -> NValue t f m -> m a
  processKeys kys v =
    list
      (h v)
      (\ ((k : ks) :: [VarName]) ->
        do
          v' <- demand v
          case (k, v') of
            (Text.decimal . coerce -> Right (n,""), NVList xs) -> processKeys ks $ xs !! n
            (_,         NVSet _ xs) ->
              maybe
                (errorWithoutStackTrace $ "Set does not contain key ''" <> show k <> "''.")
                (processKeys ks)
                (M.lookup k xs)
            (_, _) -> errorWithoutStackTrace $ "Expected a set or list for selector '" <> show k <> "', but got: " <> show v
      )
      kys
