{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Nix.Cited.Basic where

import           Control.Comonad                ( Comonad )
import           Control.Comonad.Env            ( ComonadEnv )
import           Control.Monad.Free
import           GHC.Generics
import           Nix.Cited
import           Nix.Frames
import           Nix.Thunk
import           Nix.Value

newtype CitedT (f :: * -> *) m a = CitedT { unCitedT :: m a }

newtype Cited f m a = Cited { getCited :: NCited m (NValue f m) a }
  deriving
    ( Generic
    , Typeable
    , Functor
    , Applicative
    , Foldable
    , Traversable
    , Comonad
    )

deriving instance t ~ Thunk m => ComonadEnv [Provenance m (Free (NValue' f m) t)] (Cited f m)

instance t ~ Thunk m => HasCitations1 m (Free (NValue' f m) t) (Cited f m) where
  citations1 (Cited c) = citations c
  addProvenance1 x (Cited c) = Cited (addProvenance x c)

{-
instance ( Has e Options
         , Framed e m
         , MonadThunk m
         , Typeable m
         , Typeable f
         , MonadCatch m
         )
  => MonadThunk (CitedT f m) where
  type Thunk (CitedT f m) = Cited f m (Thunk m)
  type ThunkValue (CitedT f m) = ThunkValue m
  thunk mv = do
    opts :: Options <- asks (view hasLens)

    --TODO: Can we handle `thunks opts == false` by not using CitedT at all?
    if thunks opts
      then do
        frames :: Frames <- asks (view hasLens)

        -- Gather the current evaluation context at the time of thunk
        -- creation, and record it along with the thunk.
        let go (fromException ->
                    Just (EvaluatingExpr scope
                             (Fix (Compose (Ann s e))))) =
                let e' = Compose (Ann s (Nothing <$ e))
                in [Provenance scope e']
            go _ = []
            ps = concatMap (go . frame) frames

        lift $ fmap (Cited . NCited ps) . thunk $ mv
      else fmap (Cited . NCited []) . thunk $ mv

  queryM (Cited (NCited _ t)) = queryM t

  -- | The ThunkLoop exception is thrown as an exception with MonadThrow,
  --   which does not capture the current stack frame information to provide
  --   it in a NixException, so we catch and re-throw it here using
  --   'throwError' from Frames.hs.
  force (Cited (NCited ps t)) f =
    catch go (throwError @ThunkLoop)
   where
    go = case ps of
      [] -> force t f
      Provenance scope e@(Compose (Ann s _)) : _ ->
        withFrame Info (ForcingExpr scope (wrapExprLoc s e)) (force t f)

  forceEff (Cited (NCited ps t)) f = catch
    go
    (throwError @ThunkLoop)
   where
    go = case ps of
      [] -> forceEff t f
      Provenance scope e@(Compose (Ann s _)) : _ ->
        withFrame Info (ForcingExpr scope (wrapExprLoc s e)) (forceEff t f)

  further (Cited (NCited ps t)) f = Cited . NCited ps <$> further t f
-}
