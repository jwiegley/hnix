{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

module Nix.Lint where

import           Prelude                 hiding ( head
                                                , force
                                                )
import           Nix.Utils
import           Control.Monad                  ( foldM )
import           Control.Monad.Catch
import           Control.Monad.Fix
import           Control.Monad.Ref
import           Control.Monad.ST
import qualified Data.HashMap.Lazy             as M
-- Plese, use NonEmpty
import           Data.List
import qualified Data.List.NonEmpty            as NE
import qualified Data.Text                     as Text
import qualified Text.Show
import           Nix.Atoms
import           Nix.Context
import           Nix.Convert
import           Nix.Eval                       ( MonadEval(..) )
import qualified Nix.Eval                      as Eval
import           Nix.Expr
import           Nix.Frames
import           Nix.Fresh
import           Nix.String
import           Nix.Options
import           Nix.Scope
import           Nix.Thunk
import           Nix.Thunk.Basic
import           Nix.Value.Monad

data TAtom
  = TInt
  | TFloat
  | TBool
  | TNull
  deriving (Show, Eq, Ord)

data NTypeF (m :: Type -> Type) r
  = TConstant [TAtom]
  | TStr
  | TList r
  | TSet (Maybe (AttrSet r))
  | TClosure (Params ())
  | TPath
  | TBuiltin Text (Symbolic m -> m r)
  deriving Functor

compareTypes :: NTypeF m r -> NTypeF m r -> Ordering
compareTypes (TConstant _)  (TConstant _)  = EQ
compareTypes (TConstant _)  _              = LT
compareTypes _              (TConstant _)  = GT
compareTypes TStr           TStr           = EQ
compareTypes TStr           _              = LT
compareTypes _              TStr           = GT
compareTypes (TList _)      (TList _)      = EQ
compareTypes (TList _)      _              = LT
compareTypes _              (TList _)      = GT
compareTypes (TSet _)       (TSet  _)      = EQ
compareTypes (TSet _)       _              = LT
compareTypes _              (TSet _)       = GT
compareTypes TClosure{}     TClosure{}     = EQ
compareTypes TClosure{}     _              = LT
compareTypes _              TClosure{}     = GT
compareTypes TPath          TPath          = EQ
compareTypes TPath          _              = LT
compareTypes _              TPath          = GT
compareTypes (TBuiltin _ _) (TBuiltin _ _) = EQ

data NSymbolicF r
  = NAny
  | NMany [r]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SThunk (m :: Type -> Type) = NThunkF m (Symbolic m)

type SValue (m :: Type -> Type) = Ref m (NSymbolicF (NTypeF m (Symbolic m)))

data Symbolic m = SV { getSV :: SValue m } | ST { getST :: SThunk m }

instance Show (Symbolic m) where
  show _ = "<symbolic>"

everyPossible
  :: MonadAtomicRef m
  => m (Symbolic m)
everyPossible = packSymbolic NAny

mkSymbolic
  :: MonadAtomicRef m
  => [NTypeF m (Symbolic m)]
  -> m (Symbolic m)
mkSymbolic xs = packSymbolic (NMany xs)

packSymbolic
  :: MonadAtomicRef m
  => NSymbolicF (NTypeF m (Symbolic m))
  -> m (Symbolic m)
packSymbolic = fmap SV . newRef

unpackSymbolic
  :: (MonadAtomicRef m, MonadThunkId m, MonadCatch m)
  => Symbolic m
  -> m (NSymbolicF (NTypeF m (Symbolic m)))
unpackSymbolic = readRef . getSV <=< demand

type MonadLint e m =
  ( Scoped (Symbolic m) m
  , Framed e m
  , MonadAtomicRef m
  , MonadCatch m
  , MonadThunkId m
  )

symerr :: forall e m a . MonadLint e m => Text -> m a
symerr = evalError @(Symbolic m) . ErrorCall . toString

renderSymbolic :: MonadLint e m => Symbolic m -> m Text
renderSymbolic = unpackSymbolic >=> \case
  NAny     -> pure "<any>"
  NMany xs -> fmap (Text.intercalate ", ") $ forM xs $ \case
    TConstant ys -> fmap (Text.intercalate ", ") $ forM ys $ pure . \case
      TInt   -> "int"
      TFloat -> "float"
      TBool  -> "bool"
      TNull  -> "null"
    TStr    -> pure "string"
    TList r -> do
      x <- renderSymbolic =<< demand r
      pure $ "[" <> x <> "]"
    TSet Nothing  -> pure "<any set>"
    TSet (Just s) -> do
      x <- traverse (renderSymbolic <=< demand) s
      pure $ "{" <> show x <> "}"
    f@(TClosure p) -> do
      (args, sym) <- do
        f' <- mkSymbolic [f]
        lintApp (NAbs (void p) ()) f' everyPossible
      args' <- traverse renderSymbolic args
      sym'  <- renderSymbolic sym
      pure $ "(" <> show args' <> " -> " <> sym' <> ")"
    TPath          -> pure "path"
    TBuiltin _n _f -> pure "<builtin function>"

-- This function is order and uniqueness preserving (of types).
merge
  :: forall e m
   . MonadLint e m
  => NExprF ()
  -> [NTypeF m (Symbolic m)]
  -> [NTypeF m (Symbolic m)]
  -> m [NTypeF m (Symbolic m)]
merge context = go
 where
  go
    :: [NTypeF m (Symbolic m)]
    -> [NTypeF m (Symbolic m)]
    -> m [NTypeF m (Symbolic m)]
  go []       _        = stub
  go _        []       = stub
  go (x : xs) (y : ys) = case (x, y) of
    (TStr , TStr ) -> (TStr :) <$> go xs ys
    (TPath, TPath) -> (TPath :) <$> go xs ys
    (TConstant ls, TConstant rs) ->
      (TConstant (ls `intersect` rs) :) <$> go xs ys
    (TList l, TList r) ->
      (\l' ->
        (\r' -> do
          m <- defer $ unify context l' r'
          (TList m :) <$> go xs ys
        ) =<< demand r
      ) =<< demand l
    (TSet x       , TSet Nothing ) -> (TSet x :) <$> go xs ys
    (TSet Nothing , TSet x       ) -> (TSet x :) <$> go xs ys
    (TSet (Just l), TSet (Just r)) -> do
      m <- sequenceA $ M.intersectionWith
        (\ i j ->
          do
            i'' <- demand =<< i
            j'' <- demand =<< j
            (defer . unify context i'') j''
        )
        (pure <$> l)
        (pure <$> r)
      bool
        id
        ((TSet (pure m) :) <$>)
        (not $ M.null m)
        (go xs ys)

    (TClosure{}, TClosure{}) ->
      throwError $ ErrorCall "Cannot unify functions"
    (TBuiltin _ _, TBuiltin _ _) ->
      throwError $ ErrorCall "Cannot unify builtin functions"
    _ | compareTypes x y == LT -> go xs (y : ys)
      | compareTypes x y == GT -> go (x : xs) ys
      | otherwise              -> error "impossible"

{-
    mergeFunctions pl nl fl pr fr xs ys = do
        m <- sequenceA $ M.intersectionWith
            (\i j -> i >>= \i' -> j >>= \j' -> case (i', j') of
                    (Nothing, Nothing) -> pure $ pure Nothing
                    (_, Nothing) -> pure Nothing
                    (Nothing, _) -> pure Nothing
                    (Just i'', Just j'') ->
                        pure . pure <$> unify context i'' j'')
            (pure <$> pl) (pure <$> pr)
        let Just m' = sequenceA $ M.filter isJust m
        if M.null m'
            then go xs ys
            else do
                g <- unify context fl fr
                (TClosure (ParamSet m' False nl) g :)
                    <$> go xs ys
-}

-- | Result @== NMany []@ -> @unify@ fails.
unify
  :: forall e m
   . MonadLint e m
  => NExprF ()
  -> Symbolic m
  -> Symbolic m
  -> m (Symbolic m)
unify context (SV x) (SV y) = do
  x' <- readRef x
  y' <- readRef y
  case (x', y') of
    (NAny, _) -> do
      writeRef x y'
      pure $ SV y
    (_, NAny) -> do
      writeRef y x'
      pure $ SV x
    (NMany xs, NMany ys) -> do
      m <- merge context xs ys
      bool
        (do
          writeRef x   (NMany m)
          writeRef y   (NMany m)
          packSymbolic (NMany m)
        )
        (do
              -- x' <- renderSymbolic (Symbolic x)
              -- y' <- renderSymbolic (Symbolic y)
          throwError $ ErrorCall "Cannot unify "
                  -- <> show x' <> " with " <> show y'
                  --  <> " in context: " <> show context
        )
        (null m)
unify _ _ _ = error "The unexpected hath transpired!"

-- These aren't worth defining yet, because once we move to Hindley-Milner,
-- we're not going to be managing Symbolic values this way anymore.

instance ToValue Bool m (Symbolic m) where

instance ToValue [Symbolic m] m (Symbolic m) where

instance FromValue NixString m (Symbolic m) where

instance FromValue (AttrSet (Symbolic m), PositionSet) m (Symbolic m) where

instance ToValue (AttrSet (Symbolic m), PositionSet) m (Symbolic m) where

instance (MonadThunkId m, MonadAtomicRef m, MonadCatch m)
  => MonadValue (Symbolic m) m where

  defer :: m (Symbolic m) -> m (Symbolic m)
  defer = fmap ST . thunk

  demand :: Symbolic m -> m (Symbolic m)
  demand (ST v)= demand =<< force v
  demand (SV v)= pure (SV v)


instance (MonadThunkId m, MonadAtomicRef m, MonadCatch m)
  => MonadValueF (Symbolic m) m where

  demandF :: (Symbolic m -> m r) -> Symbolic m -> m r
  demandF f (ST v)= demandF f =<< force v
  demandF f (SV v)= f (SV v)


instance MonadLint e m => MonadEval (Symbolic m) m where
  freeVariable var = symerr $ "Undefined variable '" <> coerce var <> "'"

  attrMissing ks ms =
    evalError @(Symbolic m) $ ErrorCall $ toString $
      maybe
        ("Inheriting unknown attribute: " <> attr)
        (\ s ->  "Could not look up attribute " <> attr <> " in " <> show s)
        ms
   where
    attr = Text.intercalate "." $ NE.toList $ coerce <$> ks

  evalCurPos = do
    f <- mkSymbolic [TPath]
    l <- mkSymbolic [TConstant [TInt]]
    c <- mkSymbolic [TConstant [TInt]]
    mkSymbolic [TSet (pure (M.fromList [("file", f), ("line", l), ("col", c)]))]

  evalConstant c = mkSymbolic [go c]
   where
    go =
      \case
        NURI   _ -> TStr
        NInt   _ -> TConstant [TInt]
        NFloat _ -> TConstant [TFloat]
        NBool  _ -> TConstant [TBool]
        NNull    -> TConstant [TNull]

  evalString      = const $ mkSymbolic [TStr]
  evalLiteralPath = const $ mkSymbolic [TPath]
  evalEnvPath     = const $ mkSymbolic [TPath]

  evalUnary op arg =
    unify (void (NUnary op arg)) arg =<< mkSymbolic [TConstant [TInt, TBool]]

  evalBinary = lintBinaryOp

  -- The scope is deliberately wrapped in a thunk here, since it is evaluated
  -- each time a name is looked up within the weak scope, and we want to be
  -- sure the action it evaluates is to force a thunk, so its value is only
  -- computed once.
  evalWith scope body =
    do
      s <- unpackSymbolic =<< demand =<< defer scope

      pushWeakScope
        (case s of
          NMany [TSet (Just s')] -> pure s'
          NMany [TSet Nothing] -> error "NYI: with unknown"
          _ -> throwError $ ErrorCall "scope must be a set in with statement"
        )
        body

  evalIf cond t f =
    do
      t' <- t
      f' <- f
      let e = NIf cond t' f'

      _ <- unify (void e) cond =<< mkSymbolic [TConstant [TBool]]
      unify (void e) t' f'

  evalAssert cond body =
    do
      body' <- body
      let e = NAssert cond body'
      _ <- unify (void e) cond =<< mkSymbolic [TConstant [TBool]]
      pure body'

  evalApp = (fmap snd .) . lintApp (NBinary NApp () ())
  evalAbs params _ = mkSymbolic [TClosure (void params)]

  evalError = throwError

lintBinaryOp
  :: forall e m
   . (MonadLint e m, MonadEval (Symbolic m) m)
  => NBinaryOp
  -> Symbolic m
  -> m (Symbolic m)
  -> m (Symbolic m)
lintBinaryOp op lsym rarg =
  do
    rsym <- rarg
    y    <- defer everyPossible

    case op of
      NApp    -> symerr "lintBinaryOp:NApp: should never get here"
      _ -> check lsym rsym $
        case op of
          NEq     -> [TConstant [TInt, TBool, TNull], TStr, TList y]
          NNEq    -> [TConstant [TInt, TBool, TNull], TStr, TList y]

          NLt     -> [TConstant [TInt, TBool, TNull]]
          NLte    -> [TConstant [TInt, TBool, TNull]]
          NGt     -> [TConstant [TInt, TBool, TNull]]
          NGte    -> [TConstant [TInt, TBool, TNull]]

          NAnd    -> [TConstant [TBool]]
          NOr     -> [TConstant [TBool]]
          NImpl   -> [TConstant [TBool]]

          -- jww (2018-04-01): NYI: Allow Path + Str
          NPlus   -> [TConstant [TInt], TStr, TPath]
          NMinus  -> [TConstant [TInt]]
          NMult   -> [TConstant [TInt]]
          NDiv    -> [TConstant [TInt]]

          NUpdate -> [TSet mempty]

          NConcat -> [TList y]
#if __GLASGOW_HASKELL__ < 900
          _ -> fail "Should not be possible"  -- symerr or this fun signature should be changed to work in type scope
#endif
 where
  check lsym rsym xs =
    do
      let e = NBinary op lsym rsym

      m <- mkSymbolic xs
      _ <- unify (void e) lsym m
      _ <- unify (void e) rsym m
      unify (void e) lsym rsym

infixl 1 `lintApp`
lintApp
  :: forall e m
   . MonadLint e m
  => NExprF ()
  -> Symbolic m
  -> m (Symbolic m)
  -> m (HashMap VarName (Symbolic m), Symbolic m)
lintApp context fun arg =
  (\case
    NAny ->
      throwError $ ErrorCall "Cannot apply something not known to be a function"
    NMany xs -> do
      (args, ys) <- fmap unzip $ forM xs $ \case
        TClosure _params ->
          (\case
            NAny -> do
              error "NYI"

            NMany [TSet (Just _)] -> do
              error "NYI"

            NMany _ -> throwError $ ErrorCall "NYI: lintApp NMany not set"
          ) =<< unpackSymbolic =<< arg
        TBuiltin _ _f -> throwError $ ErrorCall "NYI: lintApp builtin"
        TSet _m       -> throwError $ ErrorCall "NYI: lintApp Set"
        _x            -> throwError $ ErrorCall "Attempt to call non-function"

      y <- everyPossible
      (head args, ) <$> foldM (unify context) y ys
  ) =<< unpackSymbolic fun

newtype Lint s a = Lint
  { runLint :: ReaderT (Context (Lint s) (Symbolic (Lint s))) (FreshIdT Int (ST s)) a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFix
    , MonadReader (Context (Lint s) (Symbolic (Lint s)))
    , MonadThunkId
    , MonadRef
    , MonadAtomicRef
    )

instance MonadThrow (Lint s) where
  throwM e = Lint $ ReaderT $ const (throw e)

instance MonadCatch (Lint s) where
  catch _m _h = Lint $ ReaderT $ const (fail "Cannot catch in 'Lint s'")

runLintM :: Options -> Lint s a -> ST s a
runLintM opts action = do
  i <- newRef (1 :: Int)
  runFreshIdT i $ (`runReaderT` newContext opts) $ runLint action

symbolicBaseEnv
  :: Monad m
  => m (Scopes m (Symbolic m))
symbolicBaseEnv = pure mempty

lint :: Options -> NExprLoc -> ST s (Symbolic (Lint s))
lint opts expr =
  runLintM opts $
    do
      basis <- symbolicBaseEnv

      pushScopes
        basis
        (adi
          Eval.addSourcePositions
          Eval.evalContent
          expr
        )

instance
  Scoped (Symbolic (Lint s)) (Lint s) where
  currentScopes = currentScopesReader
  clearScopes   = clearScopesReader @(Lint s) @(Symbolic (Lint s))
  pushScopes    = pushScopesReader
  lookupVar     = lookupVarReader
