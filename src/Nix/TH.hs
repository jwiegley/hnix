{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}

module Nix.TH where

import           Data.Fix                       ( Fix(..) )
import           Data.Generics.Aliases          ( extQ )
import qualified Data.Set                      as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Syntax    as TH
import           Language.Haskell.TH.Quote
import           Nix.Atoms
import           Nix.Expr
import           Nix.Parser

quoteExprExp :: String -> ExpQ
quoteExprExp s = do
  expr <- parseExpr s
  dataToExpQ
    (extQOnFreeVars metaExp expr `extQ` (pure . (TH.lift :: Text -> Q Exp)))
    expr

quoteExprPat :: String -> PatQ
quoteExprPat s = do
  expr <- parseExpr s
  dataToPatQ
    (extQOnFreeVars metaPat expr)
    expr

-- | Helper function.
extQOnFreeVars
  :: ( Typeable b
    , Typeable loc
    )
  => ( Set VarName
    -> loc
    -> Maybe q
    )
  -> NExpr
  -> b
  -> Maybe q
extQOnFreeVars f e = extQ (const Nothing) (f $ freeVars e)

parseExpr :: (MonadFail m, ToText a) => a -> m NExpr
parseExpr s =
  either
    (fail . show)
    pure
    (parseNixText $ toText s)

freeVars :: NExpr -> Set VarName
freeVars e = case unFix e of
  (NConstant    _               ) -> mempty
  (NStr         string          ) -> mapFreeVars string
  (NSym         var             ) -> one var
  (NList        list            ) -> mapFreeVars list
  (NSet   NonRecursive  bindings) -> bindFreeVars bindings
  (NSet   Recursive     bindings) -> diffBetween bindFreeVars bindDefs bindings
  (NLiteralPath _               ) -> mempty
  (NEnvPath     _               ) -> mempty
  (NUnary       _    expr       ) -> freeVars expr
  (NBinary      _    left right ) -> collectFreeVars left right
  (NSelect      orExpr expr path) ->
    Set.unions
      [ freeVars expr
      , pathFree path
      , maybe mempty freeVars orExpr
      ]
  (NHasAttr expr            path) -> freeVars expr <> pathFree path
  (NAbs     (Param varname) expr) -> Set.delete varname (freeVars expr)
  (NAbs (ParamSet set _ varname) expr) ->
    -- Include all free variables from the expression and the default arguments
    freeVars expr <>
    -- But remove the argument name if existing, and all arguments in the parameter set
    Set.difference
      (Set.unions $ freeVars <$> mapMaybe snd set)
      (Set.difference
        (maybe mempty one varname)
        (Set.fromList $ fst <$> set)
      )
  (NLet         bindings expr   ) ->
    freeVars expr <>
    diffBetween bindFreeVars bindDefs bindings
  (NIf          cond th   el    ) -> Set.unions $ freeVars <$> [cond, th, el]
  -- Evaluation is needed to find out whether x is a "real" free variable in `with y; x`, we just include it
  -- This also makes sense because its value can be overridden by `x: with y; x`
  (NWith        set  expr       ) -> collectFreeVars set expr
  (NAssert      assertion expr  ) -> collectFreeVars assertion expr
  (NSynHole     _               ) -> mempty

 where

  diffBetween :: (a -> Set VarName) -> (a -> Set VarName) -> a -> Set VarName
  diffBetween g f b = Set.difference (g b) (f b)

  collectFreeVars :: NExpr -> NExpr -> Set VarName
  collectFreeVars = (<>) `on` freeVars

  bindDefs :: Foldable t => t (Binding NExpr) -> Set VarName
  bindDefs = foldMap bind1Def
   where
    bind1Def :: Binding r -> Set VarName
    bind1Def (Inherit   Nothing                  _    _) = mempty
    bind1Def (Inherit  (Just _                 ) keys _) = Set.fromList $ mapMaybe staticKey keys
    bind1Def (NamedVar (StaticKey  varname :| _) _    _) = one varname
    bind1Def (NamedVar (DynamicKey _       :| _) _    _) = mempty

  bindFreeVars :: Foldable t => t (Binding NExpr) -> Set VarName
  bindFreeVars = foldMap bind1Free
   where
    bind1Free :: Binding NExpr -> Set VarName
    bind1Free (Inherit  Nothing     keys _) = Set.fromList $ mapMaybe staticKey keys
    bind1Free (Inherit (Just scope) _    _) = freeVars scope
    bind1Free (NamedVar path        expr _) = pathFree path <> freeVars expr

  staticKey :: NKeyName r -> Maybe VarName
  staticKey (StaticKey  varname) = pure varname
  staticKey (DynamicKey _      ) = Nothing

  pathFree :: NAttrPath NExpr -> Set VarName
  pathFree = foldMap mapFreeVars

  mapFreeVars :: Foldable t => t NExpr -> Set VarName
  mapFreeVars = foldMap freeVars


class ToExpr a where
  toExpr :: a -> NExprLoc

instance ToExpr NExprLoc where
  toExpr = id

instance ToExpr VarName where
  toExpr = Fix . NSym_ nullSpan

instance ToExpr Int where
  toExpr = Fix . NConstant_ nullSpan . NInt . fromIntegral

instance ToExpr Integer where
  toExpr = Fix . NConstant_ nullSpan . NInt

instance ToExpr Float where
  toExpr = Fix . NConstant_ nullSpan . NFloat

metaExp :: Set VarName -> NExprLoc -> Maybe ExpQ
metaExp fvs (Fix (NSym_ _ x)) | x `Set.member` fvs =
  pure [| toExpr $(varE (mkName $ toString x)) |]
metaExp _ _ = Nothing

metaPat :: Set VarName -> NExprLoc -> Maybe PatQ
metaPat fvs (Fix (NSym_ _ x)) | x `Set.member` fvs =
  pure $ varP $ mkName $ toString x
metaPat _ _ = Nothing

-- Use of @QuasiQuoter@ requires @String@.
-- After @Text -> String@ migrations done, _maybe_ think to use @QuasiText@.
nix :: QuasiQuoter
nix = QuasiQuoter { quoteExp = quoteExprExp, quotePat = quoteExprPat }
