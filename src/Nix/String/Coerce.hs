{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Nix.String.Coerce where

import           Control.Monad
import           Control.Monad.Catch     hiding ( catchJust )
import qualified Data.HashMap.Lazy             as M
import qualified Data.Text                     as Text
import           Nix.Atoms
import           Nix.Effects
import           Nix.Frames
import           Nix.String
import           Nix.Value
import           Nix.Value.Monad

#ifdef MIN_VERSION_ghc_datasize
#if MIN_VERSION_ghc_datasize(0,2,0)
import           GHC.DataSize
#endif
#endif

-- | Data type to avoid boolean blindness on what used to be called coerceMore
data CoercionLevel
  = CoerceStringy
  -- ^ Coerce only stringlike types: strings, paths, and appropriate sets
  | CoerceAny
  -- ^ Coerce everything but functions
  deriving (Eq,Ord,Enum,Bounded)

-- | Data type to avoid boolean blindness on what used to be called copyToStore
data CopyToStoreMode
  = CopyToStore
  -- ^ Add paths to the store as they are encountered
  | DontCopyToStore
  -- ^ Add paths to the store as they are encountered
  deriving (Eq,Ord,Enum,Bounded)

coerceToString
  :: ( Framed e m
     , MonadStore m
     , MonadThrow m
     , MonadDataErrorContext f m
     , MonadValue (NValue f m) m
     )
  => (NValue f m -> NValue f m -> m (NValue f m))
  -> CopyToStoreMode
  -> CoercionLevel
  -> NValue f m
  -> m NixString
coerceToString call ctsm clevel = go
 where
  go x = demand x $ \case
    NVConstant (NBool b)
      |
        -- TODO Return a singleton for "" and "1"
        b && clevel == CoerceAny -> pure
      $  makeNixStringWithoutContext "1"
      | clevel == CoerceAny -> pure $ makeNixStringWithoutContext ""
    NVConstant (NInt n) | clevel == CoerceAny ->
      pure $ makeNixStringWithoutContext $ Text.pack $ show n
    NVConstant (NFloat n) | clevel == CoerceAny ->
      pure $ makeNixStringWithoutContext $ Text.pack $ show n
    NVConstant NNull | clevel == CoerceAny ->
      pure $ makeNixStringWithoutContext ""
    NVStr ns -> pure ns
    NVPath p
      | ctsm == CopyToStore -> storePathToNixString <$> addPath p
      | otherwise -> pure $ makeNixStringWithoutContext $ Text.pack p
    NVList l | clevel == CoerceAny ->
      nixStringUnwords <$> traverse (`demand` go) l

    v@(NVSet s _) | Just p <- M.lookup "__toString" s ->
      demand p $ (`call` v) >=> go

    NVSet s _ | Just p <- M.lookup "outPath" s -> demand p go

    v -> throwError $ ErrorCall $ "Expected a string, but saw: " <> show v

  nixStringUnwords =
    intercalateNixString (makeNixStringWithoutContext " ")
  storePathToNixString :: StorePath -> NixString
  storePathToNixString sp = makeNixStringWithSingletonContext
    t
    (StringContext t DirectPath)
    where t = Text.pack $ unStorePath sp

