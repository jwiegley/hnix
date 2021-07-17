{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-} -- 2021-07-05: Due to hashing Haskell IT system situation, in HNix we currently ended-up with 2 hash package dependencies @{hashing, cryptonite}@

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Code that implements Nix builtins. Lists the functions that are built into the Nix expression evaluator. Some built-ins (aka `derivation`), are always in the scope, so they can be accessed by the name. To keap the namespace clean, most built-ins are inside the `builtins` scope - a set that contains all what is a built-in.
module Nix.Builtins
  ( withNixContext
  , builtins
  )
where


import           Prelude                 hiding ( traceM )
import           Nix.Utils
import           Control.Comonad                ( Comonad )
import           Control.Monad                  ( foldM )
import           Control.Monad.Catch            ( MonadCatch(catch) )
import           Control.Monad.ListM            ( sortByM )
import           "hashing" Crypto.Hash
import qualified "hashing" Crypto.Hash.MD5     as MD5
import qualified "hashing" Crypto.Hash.SHA1    as SHA1
import qualified "hashing" Crypto.Hash.SHA256  as SHA256
import qualified "hashing" Crypto.Hash.SHA512  as SHA512
import qualified Data.Aeson                    as A
import           Data.Align                     ( alignWith )
import           Data.Array
import           Data.Bits
import qualified Data.ByteString               as B
import           Data.ByteString.Base16        as Base16
import           Data.Char                      ( isDigit )
import           Data.Foldable                  ( foldrM )
import           Data.Fix                       ( foldFix )
import           Data.List                      ( partition )
import qualified Data.HashMap.Lazy             as M
import           Data.Scientific
import qualified Data.Set                      as S
import qualified Data.Text                     as Text
import qualified Data.Text.Lazy.Builder        as Builder
import           Data.These                     ( fromThese )
import qualified Data.Time.Clock.POSIX         as Time
import qualified Data.Vector                   as V
import           NeatInterpolation              ( text )
import           Nix.Atoms
import           Nix.Convert
import           Nix.Effects
import           Nix.Effects.Basic              ( fetchTarball )
import           Nix.Exec
import           Nix.Expr.Types
import qualified Nix.Eval                      as Eval
import           Nix.Frames
import           Nix.Json
import           Nix.Normal
import           Nix.Options
import           Nix.Parser
import           Nix.Render
import           Nix.Scope
import           Nix.String
import           Nix.String.Coerce
import           Nix.Value
import           Nix.Value.Equal
import           Nix.Value.Monad
import           Nix.XML
import           System.Nix.Base32             as Base32
import           System.FilePath
import           System.Posix.Files             ( isRegularFile
                                                , isDirectory
                                                , isSymbolicLink
                                                )
import           Text.Regex.TDFA                ( Regex
                                                , makeRegex
                                                , matchOnceText
                                                , matchAllText
                                                )


-- This is a big module. There is recursive reuse:
-- @builtins -> builtinsList -> scopedImport -> withNixContext -> builtins@,
-- since @builtins@ is self-recursive: aka we ship @builtins.builtins.builtins...@.

-- * Internal

-- ** Nix Builtins Haskell type level

newtype Prim m a = Prim { runPrim :: m a }

data BuiltinType = Normal | TopLevel
data Builtin v =
  Builtin
    { _kind   :: BuiltinType
    , mapping :: (VarName, v)
    }

-- *** @class ToBuiltin@ and its instances

-- | Types that support conversion to nix in a particular monad
class ToBuiltin t f m a | a -> m where
  toBuiltin :: Text -> a -> m (NValue t f m)

instance
  ( MonadNix e t f m
  , ToValue a m (NValue t f m)
  )
  => ToBuiltin t f m (Prim m a) where
  toBuiltin _ p = toValue =<< runPrim p

instance
  ( MonadNix e t f m
  , FromValue a m (Deeper (NValue t f m))
  , ToBuiltin t f m b
  )
  => ToBuiltin t f m (a -> b) where
  toBuiltin name f =
    pure $ nvBuiltin (coerce name) $ toBuiltin name . f <=< fromValue . Deeper

-- *** @WValue@ closure wrapper to have @Ord@

-- We wrap values solely to provide an Ord instance for genericClosure
newtype WValue t f m = WValue (NValue t f m)

instance Comonad f => Eq (WValue t f m) where
  WValue (NVConstant (NFloat x)) == WValue (NVConstant (NInt y)) =
    x == fromInteger y
  WValue (NVConstant (NInt   x)) == WValue (NVConstant (NFloat y)) =
    fromInteger x == y
  WValue (NVConstant (NInt   x)) == WValue (NVConstant (NInt   y)) = x == y
  WValue (NVConstant (NFloat x)) == WValue (NVConstant (NFloat y)) = x == y
  WValue (NVPath     x         ) == WValue (NVPath     y         ) = x == y
  WValue (NVStr x) == WValue (NVStr y) =
    stringIgnoreContext x == stringIgnoreContext y
  _ == _ = False

instance Comonad f => Ord (WValue t f m) where
  WValue (NVConstant (NFloat x)) <= WValue (NVConstant (NInt y)) =
    x <= fromInteger y
  WValue (NVConstant (NInt   x)) <= WValue (NVConstant (NFloat y)) =
    fromInteger x <= y
  WValue (NVConstant (NInt   x)) <= WValue (NVConstant (NInt   y)) = x <= y
  WValue (NVConstant (NFloat x)) <= WValue (NVConstant (NFloat y)) = x <= y
  WValue (NVPath     x         ) <= WValue (NVPath     y         ) = x <= y
  WValue (NVStr x) <= WValue (NVStr y) =
    stringIgnoreContext x <= stringIgnoreContext y
  _ <= _ = False

-- ** Helpers

nvNull
  :: MonadNix e t f m
  => NValue t f m
nvNull = nvConstant NNull

mkNVBool
  :: MonadNix e t f m
  => Bool
  -> NValue t f m
mkNVBool = nvConstant . NBool

foldNixPath
  :: forall e t f m r
   . MonadNix e t f m
  => r
  -> (FilePath -> Maybe Text -> NixPathEntryType -> r -> m r)
  -> m r
foldNixPath z f =
  do
    mres <- lookupVar "__includes"
    dirs <-
      maybe
        stub
        ((fromValue . Deeper) <=< demand)
        mres
    mPath    <- getEnvVar "NIX_PATH"
    mDataDir <- getEnvVar "NIX_DATA_DIR"
    dataDir  <-
      maybe
        getDataDir
        (pure . toString)
        mDataDir

    foldrM
      go
      z
      $ (fromInclude . stringIgnoreContext <$> dirs)
        <> maybe
            mempty
            uriAwareSplit
            mPath
        <> [ fromInclude $ "nix=" <> toText dataDir <> "/nix/corepkgs" ]
 where

  fromInclude x = (x, ) $
    bool
      PathEntryPath
      PathEntryURI
      ("://" `Text.isInfixOf` x)

  go (x, ty) rest =
    case Text.splitOn "=" x of
      [p] -> f (toString p) mempty ty rest
      [n, p] -> f (toString p) (pure n) ty rest
      _ -> throwError $ ErrorCall $ "Unexpected entry in NIX_PATH: " <> show x

attrsetGet :: MonadNix e t f m => VarName -> AttrSet (NValue t f m) -> m (NValue t f m)
attrsetGet k s =
  maybe
    (throwError $ ErrorCall $ toString @Text $ "Attribute '" <> coerce k <> "' required")
    pure
    (M.lookup k s)

data VersionComponent
  = VersionComponentPre -- ^ The string "pre"
  | VersionComponentString !Text -- ^ A string other than "pre"
  | VersionComponentNumber !Integer -- ^ A number
  deriving (Show, Read, Eq, Ord)

versionComponentToString :: VersionComponent -> Text
versionComponentToString =
  \case
    VersionComponentPre      -> "pre"
    VersionComponentString s -> s
    VersionComponentNumber n -> show n

-- | Based on https://github.com/NixOS/nix/blob/4ee4fda521137fed6af0446948b3877e0c5db803/src/libexpr/names.cc#L44
versionComponentSeparators :: String
versionComponentSeparators = ".-"

splitVersion :: Text -> [VersionComponent]
splitVersion s =
  case Text.uncons s of
    Nothing -> mempty
    Just (h, t)

      | h `elem` versionComponentSeparators -> splitVersion t

      | isDigit h ->
        let (digits, rest) = Text.span isDigit s
        in
        VersionComponentNumber
            (fromMaybe (error $ "splitVersion: couldn't parse " <> show digits) $ readMaybe $ toString digits) : splitVersion rest

      | otherwise ->
        let
          (chars, rest) =
            Text.span
              (\c -> not $ isDigit c || c `elem` versionComponentSeparators)
              s
          thisComponent =
            case chars of
              "pre" -> VersionComponentPre
              x     -> VersionComponentString x
        in
        thisComponent : splitVersion rest

compareVersions :: Text -> Text -> Ordering
compareVersions s1 s2 =
  mconcat $
    alignWith
      f
      (splitVersion s1)
      (splitVersion s2)
 where
  z = VersionComponentString ""
  f = uncurry compare . fromThese z z

splitDrvName :: Text -> (Text, Text)
splitDrvName s =
  let
    sep    = "-"
    pieces = Text.splitOn sep s
    isFirstVersionPiece p =
      case Text.uncons p of
        Just (h, _) -> isDigit h
        _           -> False
    -- Like 'break', but always puts the first item into the first result
    -- list
    breakAfterFirstItem :: (a -> Bool) -> [a] -> ([a], [a])
    breakAfterFirstItem f =
      list
        (mempty, mempty)
        (\ (h : t) -> let (a, b) = break f t in (h : a, b))
    (namePieces, versionPieces) =
      breakAfterFirstItem isFirstVersionPiece pieces
  in
  (Text.intercalate sep namePieces, Text.intercalate sep versionPieces)

splitMatches
  :: forall e t f m
   . MonadNix e t f m
  => Int
  -> [[(ByteString, (Int, Int))]]
  -> ByteString
  -> [NValue t f m]
splitMatches _ [] haystack = [thunkStr haystack]
splitMatches _ ([] : _) _ =
  fail "Fail in splitMatches: this should never happen!"
splitMatches numDropped (((_, (start, len)) : captures) : mts) haystack =
  thunkStr before : caps : splitMatches (numDropped + relStart + len)
                                        mts
                                        (B.drop len rest)
 where
  relStart       = max 0 start - numDropped
  (before, rest) = B.splitAt relStart haystack
  caps           = nvList (f <$> captures)
  f (a, (s, _))  =
    bool
      nvNull
      (thunkStr a)
      (s >= 0)

thunkStr :: Applicative f => ByteString -> NValue t f m
thunkStr s = nvStrWithoutContext $ decodeUtf8 s

hasKind
  :: forall a e t f m
   . (MonadNix e t f m, FromValue a m (NValue t f m))
  => NValue t f m
  -> m (NValue t f m)
hasKind nv =
  do
    v <- fromValueMay nv

    toValue $
      case v of
        Just (_ :: a) -> True
        _             -> False


absolutePathFromValue :: MonadNix e t f m => NValue t f m -> m FilePath
absolutePathFromValue =
  \case
    NVStr ns ->
      do
        let
          path = toString $ stringIgnoreContext ns

        unless (isAbsolute path) $ throwError $ ErrorCall $ "string " <> show path <> " doesn't represent an absolute path"
        pure path

    NVPath path -> pure path
    v           -> throwError $ ErrorCall $ "expected a path, got " <> show v


data FileType
  = FileTypeRegular
  | FileTypeDirectory
  | FileTypeSymlink
  | FileTypeUnknown
  deriving (Show, Read, Eq, Ord)

instance Convertible e t f m => ToValue FileType m (NValue t f m) where
  toValue =
    toValue . makeNixStringWithoutContext .
      \case
        FileTypeRegular   -> "regular" :: Text
        FileTypeDirectory -> "directory"
        FileTypeSymlink   -> "symlink"
        FileTypeUnknown   -> "unknown"

-- ** Builtin functions

derivationNix
  :: forall e t f m. (MonadNix e t f m, Scoped (NValue t f m) m)
  => m (NValue t f m)
derivationNix = foldFix Eval.eval $$(do
    -- This is compiled in so that we only parse it once at compile-time.
    let Right expr = parseNixText [text|
      drvAttrs @ { outputs ? [ "out" ], ... }:

      let

        strict = derivationStrict drvAttrs;

        commonAttrs = drvAttrs
          // (builtins.listToAttrs outputsList)
          // { all = map (x: x.value) outputsList;
               inherit drvAttrs;
             };

        outputToAttrListElement = outputName:
          { name = outputName;
            value = commonAttrs // {
              outPath = builtins.getAttr outputName strict;
              drvPath = strict.drvPath;
              type = "derivation";
              inherit outputName;
            };
          };

        outputsList = map outputToAttrListElement outputs;

      in (builtins.head outputsList).value|]
    [|| expr ||]
  )

nixPathNix :: MonadNix e t f m => m (NValue t f m)
nixPathNix =
  fmap
    nvList
    (foldNixPath mempty $
      \p mn ty rest ->
        pure $
          pure
            (nvSet
              mempty
              (M.fromList
                [case ty of
                  PathEntryPath -> ("path", nvPath p)
                  PathEntryURI  -> ( "uri", mkNvStr p)

                , ( "prefix", mkNvStr $ toString $ fromMaybe "" mn)
                ]
              )
            )
          <> rest
    )
 where
  mkNvStr = nvStrWithoutContext . toText

toStringNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
toStringNix = toValue <=< coerceToString callFunc DontCopyToStore CoerceAny

hasAttrNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
hasAttrNix x y =
  do
    (coerce -> key) <- fromStringNoContext =<< fromValue x
    (aset, _) <- fromValue @(AttrSet (NValue t f m), PositionSet) y

    toValue $ M.member key aset

hasContextNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
hasContextNix = toValue . stringHasContext <=< fromValue

getAttrNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
getAttrNix x y =
  do
    (coerce -> key) <- fromStringNoContext =<< fromValue x
    (aset, _) <- fromValue @(AttrSet (NValue t f m), PositionSet) y

    attrsetGet key aset

unsafeGetAttrPosNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
unsafeGetAttrPosNix nvX nvY =
  do
    x <- demand nvX
    y <- demand nvY

    case (x, y) of
      (NVStr ns, NVSet apos _) ->
        maybe
          (pure nvNull)
          toValue
          (M.lookup @VarName (coerce $ stringIgnoreContext ns) apos)
      _xy -> throwError $ ErrorCall $ "Invalid types for builtins.unsafeGetAttrPosNix: " <> show _xy

-- This function is a bit special in that it doesn't care about the contents
-- of the list.
lengthNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
lengthNix = toValue . (length :: [NValue t f m] -> Int) <=< fromValue

addNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
addNix nvX nvY =
  do
    x' <- demand nvX
    y' <- demand nvY

    case (x', y') of
      (NVConstant (NInt   x), NVConstant (NInt   y)) -> toValue (             x + y :: Integer       )
      (NVConstant (NFloat x), NVConstant (NInt   y)) -> toValue $             x + fromInteger y
      (NVConstant (NInt   x), NVConstant (NFloat y)) -> toValue $ fromInteger x + y
      (NVConstant (NFloat x), NVConstant (NFloat y)) -> toValue $             x + y
      (_x                   , _y                   ) -> throwError $ Addition _x _y

mulNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
mulNix nvX nvY =
  do
    x' <- demand nvX
    y' <- demand nvY

    case (x', y') of
      (NVConstant (NInt   x), NVConstant (NInt   y)) -> toValue (x * y :: Integer       )
      (NVConstant (NFloat x), NVConstant (NInt   y)) -> toValue (x * fromInteger y)
      (NVConstant (NInt   x), NVConstant (NFloat y)) -> toValue (fromInteger x * y)
      (NVConstant (NFloat x), NVConstant (NFloat y)) -> toValue (x * y            )
      (_x                   , _y                   ) -> throwError $ Multiplication _x _y

divNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
divNix nvX nvY =
  do
    x' <- demand nvX
    y' <- demand nvY
    case (x', y') of
      (NVConstant (NInt   x), NVConstant (NInt   y)) | y /= 0 -> toValue (  floor (fromInteger x / fromInteger y :: Double) :: Integer)
      (NVConstant (NFloat x), NVConstant (NInt   y)) | y /= 0 -> toValue $                     x / fromInteger y
      (NVConstant (NInt   x), NVConstant (NFloat y)) | y /= 0 -> toValue $         fromInteger x / y
      (NVConstant (NFloat x), NVConstant (NFloat y)) | y /= 0 -> toValue $                     x / y
      (_x                   , _y                   )         -> throwError $ Division _x _y

anyNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
anyNix f = toValue <=< anyMNix fromValue <=< traverse (callFunc f) <=< fromValue
 where
  anyMNix :: Monad m => (a -> m Bool) -> [a] -> m Bool
  anyMNix _ []       = pure False
  anyMNix p (x : xs) =
    bool
      (anyMNix p xs)
      (pure True)
      =<< p x

allNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
allNix f = toValue <=< allMNix fromValue <=< traverse (callFunc f) <=< fromValue
 where
  allMNix :: Monad m => (a -> m Bool) -> [a] -> m Bool
  allMNix _ []       = pure True
  allMNix p (x : xs) =
    bool
      (pure False)
      (allMNix p xs)
      =<< p x

foldl'Nix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
foldl'Nix f z xs =  foldM go z =<< fromValue @[NValue t f m] xs
 where
  go b a = (`callFunc` a) =<< callFunc f b

headNix :: forall e t f m. MonadNix e t f m => NValue t f m -> m (NValue t f m)
headNix =
  maybe
    (throwError $ ErrorCall "builtins.head: empty list")
    pure
  . viaNonEmpty head <=< fromValue @[NValue t f m]

tailNix :: forall e t f m. MonadNix e t f m => NValue t f m -> m (NValue t f m)
tailNix =
  maybe
    (throwError $ ErrorCall "builtins.tail: empty list")
    (pure . nvList)
  . viaNonEmpty tail <=< fromValue @[NValue t f m]

splitVersionNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
splitVersionNix v =
  do
    version <- fromStringNoContext =<< fromValue v
    pure $
      nvList $
        nvStrWithoutContext . versionComponentToString <$>
          splitVersion version

compareVersionsNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
compareVersionsNix t1 t2 =
  do
    s1 <- mkText t1
    s2 <- mkText t2

    let
      cmpVers =
        case compareVersions s1 s2 of
          LT -> -1
          EQ -> 0
          GT -> 1

    pure $ nvConstant $ NInt cmpVers

 where
  mkText = fromStringNoContext <=< fromValue

parseDrvNameNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
parseDrvNameNix drvname =
  do
    s <- fromStringNoContext =<< fromValue drvname

    let
      (name :: Text, version :: Text) = splitDrvName s

    toValue @(AttrSet (NValue t f m)) $
      M.fromList
        [ ( "name" :: VarName
          , mkNVStr name
          )
        , ( "version"
          , mkNVStr version
          )
        ]

 where
  mkNVStr = nvStrWithoutContext

matchNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
matchNix pat str =
  do
    p <- fromStringNoContext =<< fromValue pat
    ns <- fromValue str

    -- NOTE: 2018-11-19: Currently prim_match in nix/src/libexpr/primops.cc
    -- ignores the context of its second argument. This is probably a bug but we're
    -- going to preserve the behavior here until it is fixed upstream.
    -- Relevant issue: https://github.com/NixOS/nix/issues/2547
    let
      s  = stringIgnoreContext ns
      re = makeRegex p :: Regex
      mkMatch t =
        bool
          (toValue ()) -- Shorthand for Null
          (toValue $ makeNixStringWithoutContext t)
          (not $ Text.null t)

    case matchOnceText re s of
      Just ("", sarr, "") ->
        do
          let submatches = fst <$> elems sarr
          nvList <$>
            traverse
              mkMatch
              (case submatches of
                 [] -> []
                 [a] -> [a]
                 _:xs -> xs -- return only the matched groups, drop the full string
              )
      _ -> pure nvNull

splitNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
splitNix pat str =
  do
    p <- fromStringNoContext =<< fromValue pat
    ns <- fromValue str
        -- NOTE: Currently prim_split in nix/src/libexpr/primops.cc ignores the
        -- context of its second argument. This is probably a bug but we're
        -- going to preserve the behavior here until it is fixed upstream.
        -- Relevant issue: https://github.com/NixOS/nix/issues/2547
    let
      s = stringIgnoreContext ns
      regex       = makeRegex p :: Regex
      haystack = encodeUtf8 s

    pure $ nvList $ splitMatches 0 (elems <$> matchAllText regex haystack) haystack

substringNix :: forall e t f m. MonadNix e t f m => Int -> Int -> NixString -> Prim m NixString
substringNix start len str =
  Prim $
    bool
      (throwError $ ErrorCall $ "builtins.substring: negative start position: " <> show start)
      (pure $ modifyNixContents (take . Text.drop start) str)
      (start >= 0)
 where
  take =
    bool
      id  --NOTE: negative values of 'len' are OK, and mean "take everything"
      (Text.take len)
      (len >= 0)

attrNamesNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
attrNamesNix =
  (fmap (coerce :: CoerceDeeperToNValue t f m) . toValue . fmap (makeNixStringWithoutContext . coerce @VarName @Text) . sort . M.keys)
  <=< fromValue @(AttrSet (NValue t f m))

attrValuesNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
attrValuesNix nvattrs =
  do
    attrs <- fromValue @(AttrSet (NValue t f m)) nvattrs
    toValue $
      snd <$>
        sortOn
          (fst @VarName @(NValue t f m))
          (M.toList attrs)

mapNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
mapNix f =
  toValue <=<
    traverse
      (defer @(NValue t f m)
      . withFrame Debug (ErrorCall "While applying f in map:\n")
      . callFunc f
      )
      <=< fromValue @[NValue t f m]

mapAttrsNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
mapAttrsNix f xs =
  do
    nixAttrset <- fromValue @(AttrSet (NValue t f m)) xs
    let
      keyVals = M.toList nixAttrset
      keys = fst <$> keyVals

      applyFunToKeyVal (key, val) =
        do
          runFunForKey <- callFunc f $ nvStrWithoutContext (coerce key)
          callFunc runFunForKey val

    newVals <-
      traverse
        (defer @(NValue t f m) . withFrame Debug (ErrorCall "While applying f in mapAttrs:\n") . applyFunToKeyVal)
        keyVals

    toValue $ M.fromList $ zip keys newVals

filterNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
filterNix f =
  toValue <=<
    filterM
      (fromValue <=< callFunc f)
      <=< fromValue

catAttrsNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
catAttrsNix attrName xs =
  do
    n <- fromStringNoContext =<< fromValue attrName
    l <- fromValue @[NValue t f m] xs

    nvList . catMaybes <$>
      traverse
        (fmap (M.lookup (coerce @Text @VarName n)) . fromValue <=< demand)
        l

baseNameOfNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
baseNameOfNix x =
  do
    ns <- coerceToString callFunc DontCopyToStore CoerceStringy x
    pure $
      nvStr $
        modifyNixContents
          (toText . takeFileName . toString)
          ns

bitAndNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
bitAndNix x y =
  do
    a <- fromValue @Integer x
    b <- fromValue @Integer y

    toValue (a .&. b)

bitOrNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
bitOrNix x y =
  do
    a <- fromValue @Integer x
    b <- fromValue @Integer y

    toValue (a .|. b)

bitXorNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
bitXorNix x y =
  do
    a <- fromValue @Integer x
    b <- fromValue @Integer y

    toValue (a `xor` b)

builtinsBuiltinNix
  :: forall e t f m
   . MonadNix e t f m
  => m (NValue t f m)
builtinsBuiltinNix = throwError $ ErrorCall "HNix does not provide builtins.builtins at the moment. Using builtins directly should be preferred"

dirOfNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
dirOfNix nvdir =
  do
    dir <- demand nvdir

    case dir of
      NVStr ns -> pure $ nvStr $ modifyNixContents (toText . takeDirectory . toString) ns
      NVPath path -> pure $ nvPath $ takeDirectory path
      v -> throwError $ ErrorCall $ "dirOf: expected string or path, got " <> show v

-- jww (2018-04-28): This should only be a string argument, and not coerced?
unsafeDiscardStringContextNix
  :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
unsafeDiscardStringContextNix mnv = do
  ns <- fromValue mnv
  toValue $ makeNixStringWithoutContext $ stringIgnoreContext ns

-- | Evaluate `a` to WHNF to collect its topmost effect.
seqNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
seqNix a b = b <$ demand a

-- | Evaluate 'a' to NF to collect all of its effects, therefore data cycles are ignored.
deepSeqNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
deepSeqNix a b = b <$ normalForm_ a

elemNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
elemNix x = toValue <=< anyMNix (valueEqM x) <=< fromValue
 where
  anyMNix :: Monad m => (a -> m Bool) -> [a] -> m Bool
  anyMNix _ []       = pure False
  anyMNix p (x : xs) =
    bool
      (anyMNix p xs)
      (pure True)
      =<< p x

elemAtNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
elemAtNix xs n =
  do
    n' <- fromValue n
    xs' <- fromValue xs
    maybe
      (throwError $ ErrorCall $ "builtins.elem: Index " <> show n' <> " too large for list of length " <> show (length xs'))
      pure
      (xs' !!? n')

genListNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
genListNix f nixN =
  do
    n <- fromValue @Integer nixN
    bool
      (throwError $ ErrorCall $ "builtins.genList: Expected a non-negative number, got " <> show n)
      (toValue =<< traverse (defer . callFunc f <=< toValue) [0 .. n - 1])
      (n >= 0)

genericClosureNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
genericClosureNix c =
  do
  s <- fromValue @(AttrSet (NValue t f m)) c

  case (M.lookup "startSet" s, M.lookup "operator" s) of
    (Nothing    , Nothing        ) -> throwError $ ErrorCall "builtins.genericClosure: Attributes 'startSet' and 'operator' required"
    (Nothing    , Just _         ) -> throwError $ ErrorCall "builtins.genericClosure: Attribute 'startSet' required"
    (Just _     , Nothing        ) -> throwError $ ErrorCall "builtins.genericClosure: Attribute 'operator' required"
    (Just startSet, Just operator) ->
      do
        ss <- fromValue @[NValue t f m] =<< demand startSet
        op <- demand operator

        toValue @[NValue t f m] =<< snd <$> go op mempty ss
 where
  go
    :: NValue t f m
    -> Set (WValue t f m)
    -> [NValue t f m]
    -> m (Set (WValue t f m), [NValue t f m])
  go _  ks []       = pure (ks, mempty)
  go op ks (t : ts) =
    do
      v <- demand t
      k <- demand =<< attrsetGet "key" =<< fromValue @(AttrSet (NValue t f m)) v

      bool
        (do
          ys <- fromValue @[NValue t f m] =<< callFunc op v
          checkComparable k
            (case S.toList ks of
              []           -> k
              WValue j : _ -> j
            )
          (t :) <<$>> go op (S.insert (WValue k) ks) (ts <> ys)
        )
        (go op ks ts)
        (S.member (WValue k) ks)

-- | Takes:
-- 1. List of strings to match.
-- 2. List of strings to replace corresponding match occurance. (arg 1 & 2 lists matched by index)
-- 3. String to process
-- -> returns the string with requested replacements.
--
-- Example:
-- builtins.replaceStrings ["ll" "e"] [" " "i"] "Hello world" == "Hi o world".
replaceStringsNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
replaceStringsNix tfrom tto ts =
  do
    -- NixStrings have context - remember
    (fromKeys :: [NixString]) <- fromValue (Deeper tfrom)
    (toVals   :: [NixString]) <- fromValue (Deeper tto)
    (string   ::  NixString ) <- fromValue ts

    when (length fromKeys /= length toVals) $ throwError $ ErrorCall "builtins.replaceStrings: Arguments `from`&`to` construct a key-value map, so the number of their elements must always match."

    let
      --  2021-02-18: NOTE: if there is no match - the process does not changes the context, simply slides along the string.
      --  So it isbe more effective to pass the context as the first argument.
      --  And moreover, the `passOneCharNgo` passively passes the context, to context can be removed from it and inherited directly.
      --  Then the solution would've been elegant, but the Nix bug prevents elegant implementation.
      go ctx input output =
        maybe
            -- Passively pass the chars
          passOneChar
          replace
          maybePrefixMatch

       where
        -- When prefix matched something - returns (match, replacement, remainder)
        maybePrefixMatch :: Maybe (Text, NixString, Text)
        maybePrefixMatch = formMatchReplaceTailInfo <$> find ((`Text.isPrefixOf` input) . fst) fromKeysToValsMap
         where
          formMatchReplaceTailInfo = (\(m, r) -> (m, r, Text.drop (Text.length m) input))

          fromKeysToValsMap = zip (stringIgnoreContext <$> fromKeys) toVals

        -- Not passing args => It is constant that gets embedded into `go` => It is simple `go` tail recursion
        passOneChar =
          maybe
            (finish ctx output)  -- The base case - there is no chars left to process -> finish
            (\(c, i) -> go ctx i (output <> Builder.singleton c)) -- If there are chars - pass one char & continue
            (Text.uncons input)  -- chip first char

        --  2021-02-18: NOTE: rly?: toStrict . toLazyText
        --  Maybe `text-builder`, `text-show`?
        finish ctx output = makeNixString (toStrict $ Builder.toLazyText output) ctx

        replace (key, replacementNS, unprocessedInput) = replaceWithNixBug unprocessedInput updatedOutput

         where
          replaceWithNixBug =
            bool
              (go updatedCtx)  -- tail recursion
              -- Allowing match on "" is a inherited bug of Nix,
              -- when "" is checked - it always matches. And so - when it checks - it always insers a replacement, and then process simply passesthrough the char that was under match.
              --
              -- repl> builtins.replaceStrings ["" "e"] [" " "i"] "Hello world"
              -- " H e l l o   w o r l d "
              -- repl> builtins.replaceStrings ["ll" ""] [" " "i"] "Hello world"
              -- "iHie ioi iwioirilidi"
              --  2021-02-18: NOTE: There is no tests for this
              bugPassOneChar  -- augmented recursion
              isNixBugCase

          isNixBugCase = key == mempty

          updatedOutput  = output <> replacement
          updatedCtx     = ctx <> replacementCtx

          replacement    = Builder.fromText $ stringIgnoreContext replacementNS
          replacementCtx = getContext replacementNS

          -- The bug modifies the content => bug demands `pass` to be a real function =>
          -- `go` calls `pass` function && `pass` calls `go` function
          -- => mutual recusion case, so placed separately.
          bugPassOneChar input output =
            maybe
              (finish updatedCtx output)  -- The base case - there is no chars left to process -> finish
              (\(c, i) -> go updatedCtx i $ output <> Builder.singleton c) -- If there are chars - pass one char & continue
              (Text.uncons input)  -- chip first char

    toValue $ go (getContext string) (stringIgnoreContext string) mempty

removeAttrsNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
removeAttrsNix set v =
  do
    (m, p) <- fromValue @(AttrSet (NValue t f m), PositionSet) set
    (nsToRemove :: [NixString]) <- fromValue $ Deeper v
    (coerce -> toRemove) <- traverse fromStringNoContext nsToRemove
    toValue (go m toRemove, go p toRemove)
 where
  go :: forall k v . (Eq k, Hashable k) => HashMap k v -> [k] -> HashMap k v
  go = foldl' (flip M.delete)

intersectAttrsNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
intersectAttrsNix set1 set2 =
  do
    (s1, p1) <- fromValue @(AttrSet (NValue t f m), PositionSet) set1
    (s2, p2) <- fromValue @(AttrSet (NValue t f m), PositionSet) set2

    pure $ nvSet (p2 `M.intersection` p1) (s2 `M.intersection` s1)

functionArgsNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
functionArgsNix nvfun =
  do
    fun <- demand nvfun
    case fun of
      NVClosure p _ ->
        toValue @(AttrSet (NValue t f m)) $ mkNVBool <$>
          case p of
            Param name     -> one (name, False)
            ParamSet s _ _ -> isJust <$> M.fromList s
      _v -> throwError $ ErrorCall $ "builtins.functionArgs: expected function, got " <> show _v

toFileNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
toFileNix name s =
  do
    name' <- fromStringNoContext =<< fromValue name
    s'    <- fromValue s
    mres  <-
      (toFile_ `on` toString)
        name'
        (stringIgnoreContext s')

    let
      t  = coerce $ toText @FilePath $ coerce mres
      sc = StringContext t DirectPath

    toValue $ makeNixStringWithSingletonContext t sc

toPathNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
toPathNix = toValue @Path <=< fromValue @Path

pathExistsNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
pathExistsNix nvpath =
  do
    path <- demand nvpath
    toValue =<<
      case path of
        NVPath p  -> doesPathExist p
        NVStr  ns -> doesPathExist $ toString $ stringIgnoreContext ns
        _v -> throwError $ ErrorCall $ "builtins.pathExists: expected path, got " <> show _v

isAttrsNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
isAttrsNix = hasKind @(AttrSet (NValue t f m))

isListNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
isListNix = hasKind @[NValue t f m]

isIntNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
isIntNix = hasKind @Int

isFloatNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
isFloatNix = hasKind @Float

isBoolNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
isBoolNix = hasKind @Bool

isNullNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
isNullNix = hasKind @()

-- isString cannot use `hasKind` because it coerces derivationNixs to strings.
isStringNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
isStringNix nv =
  do
    v <- demand nv

    toValue $
      case v of
        NVStr{} -> True
        _       -> False

isFunctionNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
isFunctionNix nv =
  do
    v <- demand nv

    toValue $
      case v of
        NVClosure{} -> True
        _           -> False

throwNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
throwNix mnv =
  do
    ns <- coerceToString callFunc CopyToStore CoerceStringy mnv

    throwError . ErrorCall . toString $ stringIgnoreContext ns

-- | Implementation of Nix @import@ clause.
--
-- Because Nix @import@s work strictly
-- (import gets fully evaluated befor bringing it into the scope it was called from)
-- - that property raises a requirement for execution phase of the interpreter go into evaluation phase
-- & then also go into parsing phase on the imports.
-- So it is not possible (more precise - not practical) to do a full parse Nix code phase fully & then go into evaluation phase.
-- As it is not possible to "import them lazily", as import is strict & it is not possible to establish
-- what imports whould be needed up until where it would be determined & they import strictly
--
importNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
importNix = scopedImportNix $ nvSet mempty mempty

-- | @scopedImport scope path@
-- An undocumented secret powerful function.
--
-- At the same time it is strongly forbidden to be used, as prolonged use of it would bring devastating consequences.
-- As it is essentially allows rewriting(redefinition) paradigm.
--
-- Allows to import the environment into the scope of a file expression that gets imported.
-- It is as if the contents at @path@ were given to @import@ wrapped as: @with scope; path@
-- meaning:
--
-- > -- Nix pseudocode:
-- > import (with scope; path)
--
-- For example, it allows to use itself as:
-- > bar = scopedImport pkgs ./bar.nix;
-- > -- & declare @./bar.nix@ without a header, so as:
-- > stdenv.mkDerivation { ... buildInputs = [ libfoo ]; }
--
-- But that breaks the evaluation/execution sharing of the @import@s.
--
-- Function also allows to redefine or extend the builtins.
--
-- For instance, to trace all calls to function ‘map’:
--
-- >  let
-- >    overrides = {
-- >      map = f: xs: builtins.trace "call of map!" (map f xs);
--
-- >      # Propagate override by calls to import&scopedImport.
-- >      import = fn: scopedImport overrides fn;
-- >      scopedImport = attrs: fn: scopedImport (overrides // attrs) fn;
--
-- >      # Update ‘builtins’.
-- >      builtins = builtins // overrides;
-- >    };
-- >  in scopedImport overrides ./bla.nix
--
-- In the related matter the function can be added and passed around as builtin.
scopedImportNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
scopedImportNix asetArg pathArg =
  do
    s        <- fromValue @(AttrSet (NValue t f m)) asetArg
    (Path p) <- fromValue pathArg

    path  <- pathToDefaultNix @t @f @m p
    path' <-
      maybe
        (do
          traceM "No known current directory"
          pure path
        )
        (\ res ->
          do
            (Path p') <- fromValue =<< demand res

            traceM $ "Current file being evaluated is: " <> show p'
            pure $ takeDirectory p' </> path
        )
        =<< lookupVar "__cur_file"

    clearScopes @(NValue t f m)
      $ withNixContext (pure path')
      $ pushScope s
      $ importPath @t @f @m path'

getEnvNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
getEnvNix v =
  do
    s <- fromStringNoContext =<< fromValue v
    mres <- getEnvVar s

    toValue $ makeNixStringWithoutContext $
      fromMaybe mempty mres

sortNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
sortNix comp = toValue <=< sortByM (cmp comp) <=< fromValue
 where
  cmp f a b =
    do
      isLessThan <- (`callFunc` b) =<< callFunc f a
      bool
        (do
          isGreaterThan <- (`callFunc` a) =<< callFunc f b
          fromValue isGreaterThan <&>
            bool EQ GT
        )
        (pure LT)
        =<< fromValue isLessThan

lessThanNix
  :: MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
lessThanNix ta tb =
  do
    va <- demand ta
    vb <- demand tb

    let
      badType = throwError $ ErrorCall $ "builtins.lessThan: expected two numbers or two strings, got '" <> show va <> "' and '" <> show vb <> "'."

    mkNVBool <$>
      case (va, vb) of
        (NVConstant ca, NVConstant cb) ->
          case (ca, cb) of
            (NInt   a, NInt   b) -> pure $             a < b
            (NInt   a, NFloat b) -> pure $ fromInteger a < b
            (NFloat a, NInt   b) -> pure $             a < fromInteger b
            (NFloat a, NFloat b) -> pure $             a < b
            _                    -> badType
        (NVStr a, NVStr b) -> pure $ stringIgnoreContext a < stringIgnoreContext b
        _ -> badType

-- | Helper function, generalization of @concat@ operations.
concatWith
  :: forall e t f m
   . MonadNix e t f m
  => (NValue t f m -> m (NValue t f m))
  -> NValue t f m
  -> m (NValue t f m)
concatWith f =
  toValue . concat <=<
    traverse
      (fromValue @[NValue t f m] <=< f)
      <=< fromValue @[NValue t f m]

-- | Nix function of Haskell:
-- > concat :: [[a]] -> [a]
--
-- Concatenate a list of lists into a single list.
concatListsNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
concatListsNix = concatWith demand

-- | Nix function of Haskell:
-- > concatMap :: Foldable t => (a -> [b]) -> t a -> [b]
concatMapNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
concatMapNix f = concatWith (callFunc f)

listToAttrsNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
listToAttrsNix lst =
  do
    l <- fromValue @[NValue t f m] lst
    fmap
      (nvSet mempty . M.fromList . reverse)
      (traverse
        (\ nvattrset ->
          do
            a <- fromValue @(AttrSet (NValue t f m)) =<< demand nvattrset
            (coerce -> name) <- fromStringNoContext =<< fromValue =<< demand =<< attrsetGet "name" a
            val  <- attrsetGet "value" a

            pure (name, val)
        )
        l
      )

-- prim_hashString from nix/src/libexpr/primops.cc
-- fail if context in the algo arg
-- propagate context from the s arg
-- | The result coming out of hashString is base16 encoded
hashStringNix
  :: forall e t f m. MonadNix e t f m => NixString -> NixString -> Prim m NixString
hashStringNix nsAlgo ns =
  Prim $
    do
      algo <- fromStringNoContext nsAlgo
      let
        f g = pure $ modifyNixContents g ns

      case algo of
        --  2021-03-04: Pattern can not be taken-out because hashes represented as different types
        "md5"    -> f (show . mkHash @MD5.MD5)
        "sha1"   -> f (show . mkHash @SHA1.SHA1)
        "sha256" -> f (show . mkHash @SHA256.SHA256)
        "sha512" -> f (show . mkHash @SHA512.SHA512)

        _ -> throwError $ ErrorCall $ "builtins.hashString: expected \"md5\", \"sha1\", \"sha256\", or \"sha512\", got " <> show algo

       where
        -- This intermidiary `a` is only needed because of the type application
        mkHash :: (Show a, HashAlgorithm a) => Text -> a
        mkHash s = hash $ encodeUtf8 s


placeHolderNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
placeHolderNix p =
  do
    t <- fromStringNoContext =<< fromValue p
    h <-
      runPrim $
        (hashStringNix `on` makeNixStringWithoutContext)
          "sha256"
          ("nix-output:" <> t)
    toValue
      $ makeNixStringWithoutContext
      $ Text.cons '/'
      $ Base32.encode
      -- Please, stop Text -> Bytestring here after migration to Text
      $ case Base16.decode (bytes h) of -- The result coming out of hashString is base16 encoded
#if MIN_VERSION_base16_bytestring(1,0,0)
        -- Please, stop Text -> String here after migration to Text
        Left e -> error $ "Couldn't Base16 decode the text: '" <> body h <> "'.\nThe Left fail content: '" <> show e <> "'."
        Right d -> d
#else
        (d, "") -> d
        (_, e) -> error $ "Couldn't Base16 decode the text: '" <> body h <> "'.\nUndecodable remainder: '" <> show e <> "'."
#endif
    where
      bytes :: NixString -> ByteString
      bytes = encodeUtf8 . body

      body h = stringIgnoreContext h

readFileNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
readFileNix = toValue <=< Nix.Render.readFile <=< absolutePathFromValue <=< demand

findFileNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
findFileNix nvaset nvfilepath =
  do
    aset <- demand nvaset
    filePath <- demand nvfilepath

    case (aset, filePath) of
      (NVList x, NVStr ns) ->
        do
          mres <- findPath @t @f @m x $ toString $ stringIgnoreContext ns

          pure $ nvPath mres

      (NVList _, _y     ) -> throwError $ ErrorCall $ "expected a string, got " <> show _y
      (_x      , NVStr _) -> throwError $ ErrorCall $ "expected a list, got " <> show _x
      (_x      , _y     ) -> throwError $ ErrorCall $ "Invalid types for builtins.findFile: " <> show (_x, _y)

readDirNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
readDirNix nvpath =
  do
    path           <- absolutePathFromValue =<< demand nvpath
    items          <- listDirectory path

    let
      detectFileTypes item =
        do
          s <- getSymbolicLinkStatus $ path </> item
          let
            t =
              if
                | isRegularFile s  -> FileTypeRegular
                | isDirectory s    -> FileTypeDirectory
                | isSymbolicLink s -> FileTypeSymlink
                | otherwise        -> FileTypeUnknown

          pure (coerce @Text @VarName $ toText item, t) -- function indeed binds filepaths as keys (VarNames) in Nix attrset.

    itemsWithTypes <-
      traverse
        detectFileTypes
        items

    (coerce :: CoerceDeeperToNValue t f m) <$> toValue (M.fromList itemsWithTypes)

fromJSONNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
fromJSONNix nvjson =
  do
    j <- demand nvjson
    jText <- fromStringNoContext =<< fromValue j

    either
      (\ jsonError -> throwError $ ErrorCall $ "builtins.fromJSON: " <> jsonError)
      jsonToNValue
      -- do we really need to marshall Text -> ByteString -> Aeson.Value (that is a Text)
      (A.eitherDecodeStrict' @A.Value $ encodeUtf8 jText)

 where
  -- jsonToNValue :: MonadNix e t f m => A.Value -> f (NValue t f m)
  jsonToNValue :: (A.Value -> m (NValue t f m))
  jsonToNValue = \case
    A.Object m -> nvSet mempty <$> traverse jsonToNValue (M.mapKeys coerce m)
    A.Array  l -> nvList <$> traverse jsonToNValue (V.toList l)
    A.String s -> pure $ nvStrWithoutContext s
    A.Number n ->
      pure $
        nvConstant $
          either
            NFloat
            NInt
            (floatingOrInteger n)
    A.Bool   b -> pure $ mkNVBool b
    A.Null     -> pure nvNull

toJSONNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
toJSONNix = (fmap nvStr . nvalueToJSONNixString) <=< demand

toXMLNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
toXMLNix = (fmap (nvStr . toXML) . normalForm) <=< demand

typeOfNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
typeOfNix nvv =
  do
    v <- demand nvv
    let
      detectType =
        case v of
          NVConstant a ->
            case a of
              NURI   _ -> "string"
              NInt   _ -> "int"
              NFloat _ -> "float"
              NBool  _ -> "bool"
              NNull    -> "null"
          NVStr     _   -> "string"
          NVList    _   -> "list"
          NVSet     _ _ -> "set"
          NVClosure{}   -> "lambda"
          NVPath    _   -> "path"
          NVBuiltin _ _ -> "lambda"
          _             -> error "Pattern synonyms obscure complete patterns"

    toValue $ makeNixStringWithoutContext detectType

tryEvalNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
tryEvalNix e = (`catch` (pure . onError))
  (onSuccess <$> demand e)
 where
  onSuccess v =
    nvSet
      mempty
      $ M.fromList
        [ ("success", mkNVBool True)
        , ("value"  , v            )
        ]

  onError :: SomeException -> NValue t f m
  onError _ =
    nvSet
      mempty
      $ M.fromList
        $ (, mkNVBool False) <$>
          [ "success"
          , "value"
          ]

traceNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
traceNix msg action =
  do
    traceEffect @t @f @m . toString . stringIgnoreContext =<< fromValue msg
    pure action

-- Please, can function remember fail context
addErrorContextNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m  -- action
  -> m (NValue t f m)
addErrorContextNix _ = pure

execNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
execNix xs =
  do
    ls <- fromValue @[NValue t f m] xs
    xs <- traverse (coerceToString callFunc DontCopyToStore CoerceStringy) ls
    -- 2018-11-19: NOTE: Still need to do something with the context here
    -- See prim_exec in nix/src/libexpr/primops.cc
    -- Requires the implementation of EvalState::realiseContext
    exec $ stringIgnoreContext <$> xs

fetchurlNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
fetchurlNix =
  (\case
    NVSet _ s -> go (M.lookup "sha256" s) =<< demand =<< attrsetGet "url" s
    v@NVStr{} -> go Nothing v
    v -> throwError $ ErrorCall $ "builtins.fetchurl: Expected URI or set, got " <> show v
  ) <=< demand

 where
  go :: Maybe (NValue t f m) -> NValue t f m -> m (NValue t f m)
  go _msha =
    \case
      NVStr ns ->
        either -- msha
          throwError
          toValue
          =<< getURL =<< noContextAttrs ns

      v -> throwError $ ErrorCall $ "builtins.fetchurl: Expected URI or string, got " <> show v

  noContextAttrs ns =
    maybe
      (throwError $ ErrorCall "builtins.fetchurl: unsupported arguments to url")
      pure
      (getStringNoContext ns)

partitionNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
partitionNix f nvlst =
  do
    l <- fromValue @[NValue t f m] nvlst
    let
      match t = (, t) <$> (fromValue =<< callFunc f t)
    selection <- traverse match l

    let
      (right, wrong) = partition fst selection
      makeSide       = nvList . fmap snd

    toValue @(AttrSet (NValue t f m))
      $ M.fromList
          [ ("right", makeSide right)
          , ("wrong", makeSide wrong)
          ]

currentSystemNix :: MonadNix e t f m => m (NValue t f m)
currentSystemNix =
  do
    os   <- getCurrentSystemOS
    arch <- getCurrentSystemArch

    pure $ nvStrWithoutContext $ arch <> "-" <> os

currentTimeNix :: MonadNix e t f m => m (NValue t f m)
currentTimeNix =
  do
    opts :: Options <- asks $ view hasLens
    toValue @Integer $ round $ Time.utcTimeToPOSIXSeconds $ currentTime opts

derivationStrictNix :: MonadNix e t f m => NValue t f m -> m (NValue t f m)
derivationStrictNix = derivationStrict

getRecursiveSizeNix :: (MonadIntrospect m, Applicative f) => a -> m (NValue t f m)
getRecursiveSizeNix = fmap (nvConstant . NInt . fromIntegral) . recursiveSize

getContextNix
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
getContextNix v =
  do
    v' <- demand v
    case v' of
      (NVStr ns) -> do
        let context = getNixLikeContext $ toNixLikeContext $ getContext ns
        valued :: AttrSet (NValue t f m) <- sequenceA $ toValue <$> context
        pure $ nvSet mempty valued
      x -> throwError $ ErrorCall $ "Invalid type for builtins.getContext: " <> show x

appendContextNix
  :: forall e t f m
   . MonadNix e t f m
  => NValue t f m
  -> NValue t f m
  -> m (NValue t f m)
appendContextNix tx ty =
  do
    x <- demand tx
    y <- demand ty

    case (x, y) of
      (NVStr ns, NVSet _ attrs) ->
        do
          newContextValues <- traverse getPathNOuts attrs

          toValue $ addContext ns newContextValues

      _xy -> throwError $ ErrorCall $ "Invalid types for builtins.appendContext: " <> show _xy

 where
  getPathNOuts tx =
    do
      x <- demand tx

      case x of
        NVSet _ attrs->
          do
            -- TODO: Fail for unexpected keys.

            let
              getK k =
                maybe
                  (pure False)
                  (fromValue <=< demand)
                  (M.lookup k attrs)

              getOutputs =
                maybe
                  stub
                  (\ touts ->
                    do
                      outs <- demand touts

                      case outs of
                        NVList vs -> traverse (fmap stringIgnoreContext . fromValue) vs
                        _x -> throwError $ ErrorCall $ "Invalid types for context value outputs in builtins.appendContext: " <> show _x
                  )
                  (M.lookup "outputs" attrs)

            path <- getK "path"
            allOutputs <- getK "allOutputs"

            NixLikeContextValue path allOutputs <$> getOutputs

        _x -> throwError $ ErrorCall $ "Invalid types for context value in builtins.appendContext: " <> show _x

  addContext ns newContextValues =
    makeNixString
      (stringIgnoreContext ns)
      (fromNixLikeContext $
        NixLikeContext $
          M.unionWith
            (<>)
            newContextValues
            (getNixLikeContext $
              toNixLikeContext $
                getContext ns
            )
      )


-- ** @builtinsList@

builtinsList :: forall e t f m . MonadNix e t f m => m [Builtin (NValue t f m)]
builtinsList = sequence
  [ do
      version <- toValue (makeNixStringWithoutContext "2.3")
      pure $ Builtin Normal ("nixVersion", version)
  , do
      version <- toValue (5 :: Int)
      pure $ Builtin Normal ("langVersion", version)

  , add  TopLevel "abort"            throwNix -- for now
  , add2 Normal   "add"              addNix
  , add2 Normal   "addErrorContext"  addErrorContextNix
  , add2 Normal   "all"              allNix
  , add2 Normal   "any"              anyNix
  , add2 Normal   "appendContext"    appendContextNix
  , add  Normal   "attrNames"        attrNamesNix
  , add  Normal   "attrValues"       attrValuesNix
  , add  TopLevel "baseNameOf"       baseNameOfNix
  , add2 Normal   "bitAnd"           bitAndNix
  , add2 Normal   "bitOr"            bitOrNix
  , add2 Normal   "bitXor"           bitXorNix
  , add0 Normal   "builtins"         builtinsBuiltinNix
  , add2 Normal   "catAttrs"         catAttrsNix
  , add2 Normal   "compareVersions"  compareVersionsNix
  , add  Normal   "concatLists"      concatListsNix
  , add2 Normal   "concatMap"        concatMapNix
  , add' Normal   "concatStringsSep" (arity2 intercalateNixString)
  , add0 Normal   "currentSystem"    currentSystemNix
  , add0 Normal   "currentTime"      currentTimeNix
  , add2 Normal   "deepSeq"          deepSeqNix
  , add0 TopLevel "derivation"       derivationNix
  , add  TopLevel "derivationStrict" derivationStrictNix
  , add  TopLevel "dirOf"            dirOfNix
  , add2 Normal   "div"              divNix
  , add2 Normal   "elem"             elemNix
  , add2 Normal   "elemAt"           elemAtNix
  , add  Normal   "exec"             execNix
  , add0 Normal   "false"            (pure $ mkNVBool False)
  --, add  Normal   "fetchGit"         fetchGit
  --, add  Normal   "fetchMercurial"   fetchMercurial
  , add  Normal   "fetchTarball"     fetchTarball
  , add  Normal   "fetchurl"         fetchurlNix
  , add2 Normal   "filter"           filterNix
  --, add  Normal   "filterSource"     filterSource
  , add2 Normal   "findFile"         findFileNix
  , add3 Normal   "foldl'"           foldl'Nix
  , add  Normal   "fromJSON"         fromJSONNix
  --, add  Normal   "fromTOML"         fromTOML
  , add  Normal   "functionArgs"     functionArgsNix
  , add  Normal   "genericClosure"   genericClosureNix
  , add2 Normal   "genList"          genListNix
  , add2 Normal   "getAttr"          getAttrNix
  , add  Normal   "getContext"       getContextNix
  , add  Normal   "getEnv"           getEnvNix
  , add2 Normal   "hasAttr"          hasAttrNix
  , add  Normal   "hasContext"       hasContextNix
  , add' Normal   "hashString"       (hashStringNix @e @t @f @m)
  , add  Normal   "head"             headNix
  , add  TopLevel "import"           importNix
  , add2 Normal   "intersectAttrs"   intersectAttrsNix
  , add  Normal   "isAttrs"          isAttrsNix
  , add  Normal   "isBool"           isBoolNix
  , add  Normal   "isFloat"          isFloatNix
  , add  Normal   "isFunction"       isFunctionNix
  , add  Normal   "isInt"            isIntNix
  , add  Normal   "isList"           isListNix
  , add  TopLevel "isNull"           isNullNix
  , add  Normal   "isString"         isStringNix
  , add  Normal   "length"           lengthNix
  , add2 Normal   "lessThan"         lessThanNix
  , add  Normal   "listToAttrs"      listToAttrsNix
  , add2 TopLevel "map"              mapNix
  , add2 TopLevel "mapAttrs"         mapAttrsNix
  , add2 Normal   "match"            matchNix
  , add2 Normal   "mul"              mulNix
  , add0 Normal   "nixPath"          nixPathNix
  , add0 Normal   "null"             (pure nvNull)
  , add  Normal   "parseDrvName"     parseDrvNameNix
  , add2 Normal   "partition"        partitionNix
  --, add  Normal   "path"             path
  , add  Normal   "pathExists"       pathExistsNix
  , add  TopLevel "placeholder"      placeHolderNix
  , add  Normal   "readDir"          readDirNix
  , add  Normal   "readFile"         readFileNix
  , add2 TopLevel "removeAttrs"      removeAttrsNix
  , add3 Normal   "replaceStrings"   replaceStringsNix
  , add2 TopLevel "scopedImport"     scopedImportNix
  , add2 Normal   "seq"              seqNix
  , add2 Normal   "sort"             sortNix
  , add2 Normal   "split"            splitNix
  , add  Normal   "splitVersion"     splitVersionNix
  , add0 Normal   "storeDir"         (pure $ nvStrWithoutContext "/nix/store")
  --, add  Normal   "storePath"        storePath
  , add' Normal   "stringLength"     (arity1 $ Text.length . stringIgnoreContext)
  , add' Normal   "sub"              (arity2 ((-) @Integer))
  , add' Normal   "substring"        substringNix
  , add  Normal   "tail"             tailNix
  , add  TopLevel "throw"            throwNix
  , add2 Normal   "toFile"           toFileNix
  , add  Normal   "toJSON"           toJSONNix
  , add  Normal   "toPath"           toPathNix
  , add  TopLevel "toString"         toStringNix
  , add  Normal   "toXML"            toXMLNix
  , add2 TopLevel "trace"            traceNix
  , add0 Normal   "true"             (pure $ mkNVBool True)
  , add  Normal   "tryEval"          tryEvalNix
  , add  Normal   "typeOf"           typeOfNix
  --, add0 Normal   "unsafeDiscardOutputDependency" unsafeDiscardOutputDependency
  , add  Normal   "unsafeDiscardStringContext"    unsafeDiscardStringContextNix
  , add2 Normal   "unsafeGetAttrPos"              unsafeGetAttrPosNix
  , add  Normal   "valueSize"        getRecursiveSizeNix
  ]
 where
  arity1 :: (a -> b) -> (a -> Prim m b)
  arity1 f = Prim . pure . f

  arity2 :: (a -> b -> c) -> (a -> b -> Prim m c)
  arity2 f = ((Prim . pure) .) . f

  mkBuiltin :: BuiltinType -> VarName -> m (NValue t f m) -> m (Builtin (NValue t f m))
  mkBuiltin t n v = wrap t n <$> mkThunk n v
   where
    wrap :: BuiltinType -> VarName -> v -> Builtin v
    wrap t n f = Builtin t (n, f)

    mkThunk :: VarName -> m (NValue t f m) -> m (NValue t f m)
    mkThunk n = defer . withFrame Info (ErrorCall $ "While calling builtin " <> toString n <> "\n")

  hAdd
    :: ( VarName
      -> fun
      -> m (NValue t f m)
      )
    -> BuiltinType
    -> VarName
    -> fun
    -> m (Builtin (NValue t f m))
  hAdd f t n v = mkBuiltin t n $ f n v

  add0
    :: BuiltinType
    -> VarName
    -> m (NValue t f m)
    -> m (Builtin (NValue t f m))
  add0 = hAdd (\ _ x -> x)

  add
    :: BuiltinType
    -> VarName
    -> ( NValue t f m
      -> m (NValue t f m)
      )
    -> m (Builtin (NValue t f m))
  add = hAdd builtin

  add2
    :: BuiltinType
    -> VarName
    -> ( NValue t f m
      -> NValue t f m
      -> m (NValue t f m)
      )
    -> m (Builtin (NValue t f m))
  add2 = hAdd builtin2

  add3
    :: BuiltinType
    -> VarName
    -> ( NValue t f m
      -> NValue t f m
      -> NValue t f m
      -> m (NValue t f m)
      )
    -> m (Builtin (NValue t f m))
  add3 = hAdd builtin3

  add'
    :: ToBuiltin t f m a
    => BuiltinType
    -> VarName
    -> a
    -> m (Builtin (NValue t f m))
  add' = hAdd (toBuiltin . coerce)


-- * Exported

-- | Evaluate expression in the default context.
withNixContext
  :: forall e t f m r
   . (MonadNix e t f m, Has e Options)
  => Maybe FilePath
  -> m r
  -> m r
withNixContext mpath action =
  do
    base            <- builtins
    opts :: Options <- asks $ view hasLens
    let
      i = nvList $ nvStrWithoutContext . toText <$> include opts

    pushScope
      (one ("__includes", i))
      (pushScopes
        base $
        maybe
          id
          (\ path act ->
            do
              traceM $ "Setting __cur_file = " <> show path
              let ref = nvPath path
              pushScope (one ("__cur_file", ref)) act
          )
          mpath
          action
      )

builtins
  :: ( MonadNix e t f m
     , Scoped (NValue t f m) m
     )
  => m (Scopes m (NValue t f m))
builtins =
  do
    ref <- defer $ nvSet mempty <$> buildMap
    lst <- ([("builtins", ref)] <>) <$> topLevelBuiltins
    pushScope (M.fromList lst) currentScopes
 where
  buildMap
    :: ( MonadNix e t f m
      , Scoped (NValue t f m) m
      )
    => m (HashMap VarName (NValue t f m))
  buildMap         =  fmap (M.fromList . fmap mapping) builtinsList
  topLevelBuiltins = mapping <<$>> fullBuiltinsList

  fullBuiltinsList = nameBuiltins <<$>> builtinsList
   where
    nameBuiltins b@(Builtin TopLevel _) = b
    nameBuiltins (Builtin Normal nB) =
      Builtin TopLevel $ first (coerce @Text . ("__" <>) . coerce @VarName) nB

