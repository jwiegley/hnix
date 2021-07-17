{-# LANGUAGE CPP #-}

module Nix.String.Coerce where

import           Control.Monad.Catch            ( MonadThrow )
import qualified Data.HashMap.Lazy             as M
import           Nix.Atoms
import           Nix.Effects
import           Nix.Frames
import           Nix.String
import           Nix.Value
import           Nix.Value.Monad

#ifdef MIN_VERSION_ghc_datasize
import           GHC.DataSize
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
     , MonadDataErrorContext t f m
     , MonadValue (NValue t f m) m
     )
  => (NValue t f m -> NValue t f m -> m (NValue t f m))
  -> CopyToStoreMode
  -> CoercionLevel
  -> NValue t f m
  -> m NixString
coerceToString call ctsm clevel = go
 where
  go x =
    do
      x' <- demand x
      bool
        (coerceStringy x')
        (coerceAny x')
        (clevel == CoerceAny)
     where

      coerceAny x' =
        case x' of
          -- TODO Return a singleton for "" and "1"
          NVConstant (NBool b) ->
            castToNixString $
              bool
                ""
                "1"
                b
          NVConstant (NInt n) ->
            castToNixString $
              show n
          NVConstant (NFloat n) ->
            castToNixString $
              show n
          NVConstant NNull ->
            castToNixString ""
          -- NVConstant: NAtom (NURI Text) is not matched
          NVList l ->
            nixStringUnwords <$> traverse (go <=< demand) l
          v -> coerceStringy v

      coerceStringy x' =
        case x' of
          NVStr ns -> pure ns
          NVPath p ->
            bool
              (castToNixString . toText)
              (fmap storePathToNixString . addPath)
              (ctsm == CopyToStore)
              p
          v@(NVSet _ s) ->
            maybe
              (maybe
                (err v)
                (gosw False)
                (M.lookup "outPath" s)
              )
              (gosw True)
              (M.lookup "__toString" s)
           where
            gosw b p =
              do
                p' <- demand p
                bool
                  go
                  (go <=< (`call` v))
                  b
                  p'

          v -> err v
      err v = throwError $ ErrorCall $ "Expected a string, but saw: " <> show v
      castToNixString = pure . makeNixStringWithoutContext

  nixStringUnwords = intercalateNixString $ makeNixStringWithoutContext " "

  storePathToNixString :: StorePath -> NixString
  storePathToNixString sp =
    makeNixStringWithSingletonContext
      t
      (StringContext t DirectPath)
   where
    t = fromString $ coerce sp

