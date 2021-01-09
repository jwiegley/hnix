{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Nix.Exec where

import           Prelude                 hiding ( putStr
                                                , putStrLn
                                                , print
                                                )

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Catch     hiding ( catchJust )
import           Control.Monad.Fix
import           Control.Monad.Reader
import           Data.Fix
import qualified Data.HashMap.Lazy             as M
import           Data.Interned
import           Data.List
import qualified Data.List.NonEmpty            as NE
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Typeable
import           Nix.Atoms
import           Nix.Cited
import           Nix.Convert
import           Nix.Effects
import           Nix.Eval                      as Eval
import           Nix.Expr
import           Nix.Frames
import           Nix.Options
import           Nix.Pretty
import           Nix.Render
import           Nix.Scope
import           Nix.String
import           Nix.String.Coerce
import           Nix.Thunk
import           Nix.Utils
import           Nix.Value
import           Nix.Value.Equal
import           Nix.Value.Monad
import           Prettyprinter
#ifdef MIN_VERSION_pretty_show
import qualified Text.Show.Pretty as PS
#endif

#ifdef MIN_VERSION_ghc_datasize
#if MIN_VERSION_ghc_datasize(0,2,0)
import           GHC.DataSize
#endif
#endif

type MonadCited t f m
  = ( HasCitations m (NValue t f m) t
  , HasCitations1 m (NValue t f m) f
  , MonadDataContext f m
  )

nvConstantP
  :: MonadCited t f m => Provenance m (NValue t f m) -> NAtom -> NValue t f m
nvConstantP p x = addProvenance p (nvConstant x)

nvStrP
  :: MonadCited t f m
  => Provenance m (NValue t f m)
  -> NixString
  -> NValue t f m
nvStrP p ns = addProvenance p (nvStr ns)

nvPathP
  :: MonadCited t f m => Provenance m (NValue t f m) -> FilePath -> NValue t f m
nvPathP p x = addProvenance p (nvPath x)

nvListP
  :: MonadCited t f m
  => Provenance m (NValue t f m)
  -> [NValue t f m]
  -> NValue t f m
nvListP p l = addProvenance p (nvList l)

nvSetP
  :: MonadCited t f m
  => Provenance m (NValue t f m)
  -> AttrSet (NValue t f m)
  -> AttrSet SourcePos
  -> NValue t f m
nvSetP p s x = addProvenance p (nvSet s x)

nvClosureP
  :: MonadCited t f m
  => Provenance m (NValue t f m)
  -> Params ()
  -> (NValue t f m -> m (NValue t f m))
  -> NValue t f m
nvClosureP p x f = addProvenance p (nvClosure x f)

nvBuiltinP
  :: MonadCited t f m
  => Provenance m (NValue t f m)
  -> VarName
  -> (NValue t f m -> m (NValue t f m))
  -> NValue t f m
nvBuiltinP p name f = addProvenance p (nvBuiltin name f)

type MonadCitedThunks t f m
  = ( MonadThunk t m (NValue t f m)
  , MonadDataErrorContext t f m
  , HasCitations m (NValue t f m) t
  , HasCitations1 m (NValue t f m) f
  )

type MonadNix e t f m
  = ( Has e SrcSpan
  , Has e Options
  , Scoped (NValue t f m) m
  , Framed e m
  , MonadFix m
  , MonadCatch m
  , MonadThrow m
  , Alternative m
  , MonadEffects t f m
  , MonadCitedThunks t f m
  , MonadValue (NValue t f m) m
  )

data ExecFrame t f m = Assertion SrcSpan (NValue t f m)
    deriving (Show, Typeable)

instance MonadDataErrorContext t f m => Exception (ExecFrame t f m)

nverr :: forall e t f s m a . (MonadNix e t f m, Exception s) => s -> m a
nverr = evalError @(NValue t f m)

currentPos :: forall e m . (MonadReader e m, Has e SrcSpan) => m SrcSpan
currentPos = asks (view hasLens)

wrapExprLoc :: SrcSpan -> NExprLocF r -> NExprLoc
wrapExprLoc span x = Fix (Fix (NSym_ span "<?>") <$ x)

instance MonadNix e t f m => MonadEval (NValue t f m) m where
  freeVariable var =
    nverr @e @t @f
      $  ErrorCall
      $  "Undefined variable '"
      ++ Text.unpack (unintern var)
      ++ "'"

  synHole name = do
    span  <- currentPos
    scope <- currentScopes
    evalError @(NValue t f m) $ SynHole $ SynHoleInfo
      { _synHoleInfo_expr  = Fix $ NSynHole_ span name
      , _synHoleInfo_scope = scope
      }

  attrMissing ks Nothing =
    evalError @(NValue t f m)
      $  ErrorCall
      $  "Inheriting unknown attribute: "
      ++ intercalate "." (map (Text.unpack . unintern) (NE.toList ks))

  attrMissing ks (Just s) =
    evalError @(NValue t f m)
      $  ErrorCall
      $  "Could not look up attribute "
      ++ intercalate "." (map (Text.unpack . unintern) (NE.toList ks))
      ++ " in "
      ++ show (prettyNValue s)

  evalCurPos = do
    scope                  <- currentScopes
    span@(SrcSpan delta _) <- currentPos
    addProvenance @_ @_ @(NValue t f m)
        (Provenance scope (NSym_ span "__curPos"))
      <$> toValue delta

  evaledSym name val = do
    scope <- currentScopes
    span  <- currentPos
    pure $ addProvenance @_ @_ @(NValue t f m)
      (Provenance scope (NSym_ span name))
      val

  evalConstant c = do
    scope <- currentScopes
    span  <- currentPos
    pure $ nvConstantP (Provenance scope (NConstant_ span c)) c

  evalString = assembleString >=> \case
    Just ns -> do
      scope <- currentScopes
      span  <- currentPos
      pure $ nvStrP
        (Provenance
          scope
          (NStr_ span (DoubleQuoted [Plain (stringIgnoreContext ns)]))
        )
        ns
    Nothing -> nverr $ ErrorCall "Failed to assemble string"

  evalLiteralPath p = do
    scope <- currentScopes
    span  <- currentPos
    nvPathP (Provenance scope (NLiteralPath_ span p))
      <$> makeAbsolutePath @t @f @m p

  evalEnvPath p = do
    scope <- currentScopes
    span  <- currentPos
    nvPathP (Provenance scope (NEnvPath_ span p)) <$> findEnvPath @t @f @m p

  evalUnary op arg = do
    scope <- currentScopes
    span  <- currentPos
    execUnaryOp scope span op arg

  evalBinary op larg rarg = do
    scope <- currentScopes
    span  <- currentPos
    execBinaryOp scope span op larg rarg

  evalWith c b = do
    scope <- currentScopes
    span  <- currentPos
    (\b -> addProvenance (Provenance scope (NWith_ span Nothing (Just b))) b)
      <$> evalWithAttrSet c b

  evalIf c t f = do
    scope <- currentScopes
    span  <- currentPos
    fromValue c >>= \b -> if b
      then
        (\t -> addProvenance
            (Provenance scope (NIf_ span (Just c) (Just t) Nothing))
            t
          )
          <$> t
      else
        (\f -> addProvenance
            (Provenance scope (NIf_ span (Just c) Nothing (Just f)))
            f
          )
          <$> f

  evalAssert c body = fromValue c >>= \b -> do
    span <- currentPos
    if b
      then do
        scope <- currentScopes
        (\b ->
            addProvenance (Provenance scope (NAssert_ span (Just c) (Just b))) b
          )
          <$> body
      else nverr $ Assertion span c

  evalApp f x = do
    scope <- currentScopes
    span  <- currentPos
    addProvenance (Provenance scope (NBinary_ span NApp (Just f) Nothing))
      <$> (callFunc f =<< defer x)

  evalAbs p k = do
    scope <- currentScopes
    span  <- currentPos
    pure $ nvClosureP (Provenance scope (NAbs_ span (Nothing <$ p) Nothing))
                      (void p)
                      (\arg -> snd <$> k (pure arg) (\_ b -> ((), ) <$> b))

  evalError = throwError

infixl 1 `callFunc`
callFunc
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
callFunc fun arg = demand fun $ \fun' -> do
  frames :: Frames <- asks (view hasLens)
  when (length frames > 2000) $ throwError $ ErrorCall
    "Function call stack exhausted"
  case fun' of
    NVClosure _params f -> do
      f arg
    NVBuiltin name f -> do
      span <- currentPos
      withFrame Info (Calling @m @(NValue t f m) (show name) span) (f arg)
    s@(NVSet m _) | Just f <- M.lookup "__functor" m -> do
      demand f $ (`callFunc` s) >=> (`callFunc` arg)
    x -> throwError $ ErrorCall $ "Attempt to call non-function: " ++ show x

execUnaryOp
  :: (Framed e m, MonadCited t f m, Show t)
  => Scopes m (NValue t f m)
  -> SrcSpan
  -> NUnaryOp
  -> NValue t f m
  -> m (NValue t f m)
execUnaryOp scope span op arg = do
  case arg of
    NVConstant c -> case (op, c) of
      (NNeg, NInt i  ) -> unaryOp $ NInt (-i)
      (NNeg, NFloat f) -> unaryOp $ NFloat (-f)
      (NNot, NBool b ) -> unaryOp $ NBool (not b)
      _ ->
        throwError
          $  ErrorCall
          $  "unsupported argument type for unary operator "
          ++ show op
    x ->
      throwError
        $  ErrorCall
        $  "argument to unary operator"
        ++ " must evaluate to an atomic type: "
        ++ show x
 where
  unaryOp = pure . nvConstantP (Provenance scope (NUnary_ span op (Just arg)))

execBinaryOp
  :: forall e t f m
   . (MonadNix e t f m, MonadEval (NValue t f m) m)
  => Scopes m (NValue t f m)
  -> SrcSpan
  -> NBinaryOp
  -> NValue t f m
  -> m (NValue t f m)
  -> m (NValue t f m)

execBinaryOp scope span op lval rarg = case op of
  NEq   -> rarg >>= \rval -> valueEqM lval rval >>= boolOp rval
  NNEq  -> rarg >>= \rval -> valueEqM lval rval >>= boolOp rval . not
  NOr   -> fromValue lval >>= \l -> if l
             then bypass True
             else rarg >>= \rval -> fromValue rval >>= boolOp rval
  NAnd  -> fromValue lval >>= \l -> if l
             then rarg >>= \rval -> fromValue rval >>= boolOp rval
             else bypass False
  NImpl -> fromValue lval >>= \l -> if l
             then rarg >>= \rval -> fromValue rval >>= boolOp rval
             else bypass True
  _     -> rarg >>= \rval ->
             demand rval $ \rval' ->
               demand lval $ \lval' ->
                 execBinaryOpForced scope span op lval' rval'

 where
  toBoolOp :: Maybe (NValue t f m) -> Bool -> m (NValue t f m)
  toBoolOp r b = pure $ nvConstantP
    (Provenance scope (NBinary_ span op (Just lval) r))
    (NBool b)
  boolOp rval = toBoolOp (Just rval)
  bypass      = toBoolOp Nothing


execBinaryOpForced
  :: forall e t f m
   . (MonadNix e t f m, MonadEval (NValue t f m) m)
  => Scopes m (NValue t f m)
  -> SrcSpan
  -> NBinaryOp
  -> NValue t f m
  -> NValue t f m
  -> m (NValue t f m)

execBinaryOpForced scope span op lval rval = case op of
  NLt  -> compare (<)
  NLte -> compare (<=)
  NGt  -> compare (>)
  NGte -> compare (>=)
  NMinus -> numBinOp (-)
  NMult  -> numBinOp (*)
  NDiv   -> numBinOp' div (/)
  NConcat -> case (lval, rval) of
    (NVList ls, NVList rs) -> pure $ nvListP prov $ ls ++ rs
    _ -> unsupportedTypes

  NUpdate -> case (lval, rval) of
    (NVSet ls lp, NVSet rs rp) -> pure $ nvSetP prov (rs `M.union` ls) (rp `M.union` lp)
    (NVSet ls lp, NVConstant NNull) -> pure $ nvSetP prov ls lp
    (NVConstant NNull, NVSet rs rp) -> pure $ nvSetP prov rs rp
    _ -> unsupportedTypes

  NPlus -> case (lval, rval) of
    (NVConstant _, NVConstant _) -> numBinOp (+)

    (NVStr ls, NVStr rs) -> pure $ nvStrP prov (ls `mappend` rs)
    (NVStr ls, rs@NVPath{}) ->
      (\rs2 -> nvStrP prov (ls `mappend` rs2))
        <$> coerceToString callFunc CopyToStore CoerceStringy rs
    (NVPath ls, NVStr rs) -> case getStringNoContext rs of
      Just rs2 -> nvPathP prov <$> makeAbsolutePath @t @f (ls `mappend` Text.unpack rs2)
      Nothing -> throwError $ ErrorCall $
        -- data/nix/src/libexpr/eval.cc:1412
        "A string that refers to a store path cannot be appended to a path."
    (NVPath ls, NVPath rs) -> nvPathP prov <$> makeAbsolutePath @t @f (ls ++ rs)

    (ls@NVSet{}, NVStr rs) ->
      (\ls2 -> nvStrP prov (ls2 `mappend` rs))
        <$> coerceToString callFunc DontCopyToStore CoerceStringy ls
    (NVStr ls, rs@NVSet{}) ->
      (\rs2 -> nvStrP prov (ls `mappend` rs2))
        <$> coerceToString callFunc DontCopyToStore CoerceStringy rs
    _ -> unsupportedTypes

  NEq   -> alreadyHandled
  NNEq  -> alreadyHandled
  NAnd  -> alreadyHandled
  NOr   -> alreadyHandled
  NImpl -> alreadyHandled
  NApp  -> throwError $ ErrorCall $ "NApp should be handled by evalApp"

 where
  prov :: Provenance m (NValue t f m)
  prov = Provenance scope (NBinary_ span op (Just lval) (Just rval))

  toBool = pure . nvConstantP prov . NBool
  compare :: (forall a. Ord a => a -> a -> Bool) -> m (NValue t f m)
  compare op = case (lval, rval) of
    (NVConstant l, NVConstant r) -> toBool $ l `op` r
    (NVStr l, NVStr r) -> toBool $ l `op` r
    _ -> unsupportedTypes

  toInt = pure . nvConstantP prov . NInt
  toFloat = pure . nvConstantP prov . NFloat

  numBinOp :: (forall a. Num a => a -> a -> a) -> m (NValue t f m)
  numBinOp op = numBinOp' op op

  numBinOp'
    :: (Integer -> Integer -> Integer)
    -> (Float -> Float -> Float)
    -> m (NValue t f m)

  numBinOp' intOp floatOp = case (lval, rval) of
    (NVConstant l, NVConstant r) -> case (l, r) of
      (NInt   li, NInt   ri) -> toInt $ li `intOp` ri
      (NInt   li, NFloat rf) -> toFloat $ fromInteger li `floatOp` rf
      (NFloat lf, NInt   ri) -> toFloat $ lf `floatOp` fromInteger ri
      (NFloat lf, NFloat rf) -> toFloat $ lf `floatOp` rf
      _ -> unsupportedTypes
    _ -> unsupportedTypes

  unsupportedTypes = throwError $ ErrorCall $
    "Unsupported argument types for binary operator "
      ++ show op
      ++ ": "
      ++ show lval
      ++ ", "
      ++ show rval

  alreadyHandled = throwError $ ErrorCall $
    "This cannot happen: operator "
      ++ show op
      ++ " should have been handled in execBinaryOp."

-- This function is here, rather than in 'Nix.String', because of the need to
-- use 'throwError'.
fromStringNoContext :: Framed e m => NixString -> m Text
fromStringNoContext ns = case getStringNoContext ns of
  Just str -> pure str
  Nothing  -> throwError $ ErrorCall $ "expected string with no context, but got " ++ show ns

addTracing
  :: (MonadNix e t f m, Has e Options, MonadReader Int n, Alternative n)
  => Alg NExprLocF (m a)
  -> Alg NExprLocF (n (m a))
addTracing k v = do
  depth <- ask
  guard (depth < 2000)
  local succ $ do
    v'@(Compose (Ann span x)) <- sequence v
    pure $ do
      opts :: Options <- asks (view hasLens)
      let rendered = if verbose opts >= Chatty
#ifdef MIN_VERSION_pretty_show
                     then pretty $ PS.ppShow (void x)
#else
            then pretty $ show (void x)
#endif
            else prettyNix (Fix (Fix (NSym "?") <$ x))
          msg x = pretty ("eval: " ++ replicate depth ' ') <> x
      loc <- renderLocation span (msg rendered <> " ...\n")
      putStr $ show loc
      res <- k v'
      print $ msg rendered <> " ...done"
      pure res

evalExprLoc :: forall e t f m . MonadNix e t f m => NExprLoc -> m (NValue t f m)
evalExprLoc expr = do
  opts :: Options <- asks (view hasLens)
  if tracing opts
    then join . (`runReaderT` (0 :: Int)) $ adi
      (addTracing phi)
      (raise (addStackFrames @(NValue t f m) . addSourcePositions))
      expr
    else adi phi (addStackFrames @(NValue t f m) . addSourcePositions) expr
 where
  phi = Eval.eval . annotated . getCompose
  raise k f x = ReaderT $ \e -> k (\t -> runReaderT (f t) e) x

exec :: (MonadNix e t f m, MonadInstantiate m) => [String] -> m (NValue t f m)
exec args = either throwError evalExprLoc =<< exec' args

nixInstantiateExpr
  :: (MonadNix e t f m, MonadInstantiate m) => String -> m (NValue t f m)
nixInstantiateExpr s = either throwError evalExprLoc =<< instantiateExpr s
