{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PackageImports #-} -- 2021-07-05: Due to hashing Haskell IT system situation, in HNix we currently ended-up with 2 hash package dependencies @{hashing, cryptonite}@
{-# LANGUAGE ViewPatterns #-}

module Nix.Effects.Derivation ( defaultDerivationStrict ) where

import           Nix.Utils
import           Data.Char                      ( isAscii
                                                , isAlphaNum
                                                )
import qualified Data.HashMap.Lazy             as M
import qualified Data.HashMap.Strict           as MS ( insert )
import qualified Data.HashSet                  as S
import           Data.Foldable                  ( foldl )
import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set
import qualified Data.Text                     as Text

import           Text.Megaparsec
import           Text.Megaparsec.Char

import qualified "cryptonite" Crypto.Hash      as Hash -- 2021-07-05: Attrocity of Haskell hashing situation, in HNix we ended-up with 2 hash package dependencies @{hashing, cryptonite}@

import           Nix.Atoms
import           Nix.Expr.Types          hiding ( Recursive )
import           Nix.Convert
import           Nix.Effects
import           Nix.Exec                       ( MonadNix
                                                , callFunc
                                                )
import           Nix.Frames
import           Nix.Json                       ( nvalueToJSONNixString )
import           Nix.Render
import           Nix.String
import           Nix.String.Coerce
import           Nix.Value
import           Nix.Value.Monad

import qualified System.Nix.ReadonlyStore      as Store
import qualified System.Nix.Hash               as Store
import qualified System.Nix.StorePath          as Store
import Prelude hiding (readFile)


--  2021-07-17: NOTE: Derivation consists of @"keys"@ @"vals"@ (of text), so underlining type boundary currently stops here.
data Derivation = Derivation
  { name :: Text
  , outputs :: Map Text Text
  , inputs :: (Set Text, Map Text [Text])
  , platform :: Text
  , builder :: Text -- should be typed as a store path
  , args :: [ Text ]
  , env :: Map Text Text
  , mFixed :: Maybe Store.SomeNamedDigest
  , hashMode :: HashMode
  , useJson :: Bool
  }
  deriving Show

data HashMode = Flat | Recursive
  deriving (Show, Eq)

makeStorePathName :: (Framed e m) => Text -> m Store.StorePathName
makeStorePathName name = case Store.makeStorePathName name of
  Left err -> throwError $ ErrorCall $ "Invalid name '" <> show name <> "' for use in a store path: " <> err
  Right spname -> pure spname

parsePath :: (Framed e m) => Text -> m Store.StorePath
parsePath p = case Store.parsePath "/nix/store" (encodeUtf8 p) of
  Left err -> throwError $ ErrorCall $ "Cannot parse store path " <> show p <> ":\n" <> show err
  Right path -> pure path

writeDerivation :: (Framed e m, MonadStore m) => Derivation -> m Store.StorePath
writeDerivation drv@Derivation{inputs, name} = do
  let (inputSrcs, inputDrvs) = inputs
  references <- Set.fromList <$> traverse parsePath (Set.toList $ inputSrcs <> Set.fromList (Map.keys inputDrvs))
  path <- addTextToStore (Text.append name ".drv") (unparseDrv drv) (S.fromList $ Set.toList references) False
  parsePath $ toText @FilePath $ coerce path

-- | Traverse the graph of inputDrvs to replace fixed output derivations with their fixed output hash.
-- this avoids propagating changes to their .drv when the output hash stays the same.
hashDerivationModulo :: (MonadNix e t f m, MonadState (b, KeyMap Text) m) => Derivation -> m (Hash.Digest Hash.SHA256)
hashDerivationModulo
  Derivation
    { mFixed = Just (Store.SomeDigest (digest :: Hash.Digest hashType))
    , outputs
    , hashMode
    } =
  case Map.toList outputs of
    [("out", path)] -> pure $
      Hash.hash @ByteString @Hash.SHA256 $
        encodeUtf8 $
          "fixed:out"
          <> (if hashMode == Recursive then ":r" else "")
          <> ":" <> (Store.algoName @hashType)
          <> ":" <> Store.encodeDigestWith Store.Base16 digest
          <> ":" <> path
    _outputsList -> throwError $ ErrorCall $ "This is weird. A fixed output drv should only have one output named 'out'. Got " <> show _outputsList
hashDerivationModulo
  drv@Derivation
    { inputs = ( inputSrcs
               , inputDrvs
               )
    } =
  do
    cache <- gets snd
    inputsModulo <-
      Map.fromList <$>
        traverse
          (\(path, outs) ->
            maybe
              (do
                drv' <- readDerivation $ toString path
                hash <- Store.encodeDigestWith Store.Base16 <$> hashDerivationModulo drv'
                pure (hash, outs)
              )
              (\ hash -> pure (hash, outs))
              (M.lookup path cache)
          )
          (Map.toList inputDrvs)
    pure $ Hash.hash @ByteString @Hash.SHA256 $ encodeUtf8 $ unparseDrv $ drv {inputs = (inputSrcs, inputsModulo)}

unparseDrv :: Derivation -> Text
unparseDrv Derivation{..} =
  Text.append
    "Derive"
    $ parens
      [ -- outputs: [("out", "/nix/store/.....-out", "", ""), ...]
        serializeList $
          produceOutputInfo <$> Map.toList outputs
      , -- inputDrvs
        serializeList $
          (\(path, outs) ->
            parens [s path, serializeList $ s <$> sort outs]
          ) <$> Map.toList (snd inputs)
      , -- inputSrcs
        serializeList $ s <$> Set.toList (fst inputs)
      , s platform
      , s builder
      , -- run script args
        serializeList $ s <$> args
      , -- env (key value pairs)
        serializeList $ (\(k, v) -> parens [s k, s v]) <$> Map.toList env
      ]
  where
    produceOutputInfo (outputName, outputPath) =
      let prefix = if hashMode == Recursive then "r:" else "" in
      parens $ (s <$>) $ ([outputName, outputPath] <>) $
        maybe
          [mempty, mempty]
          (\ (Store.SomeDigest (digest :: Hash.Digest hashType)) ->
            [prefix <> Store.algoName @hashType, Store.encodeDigestWith Store.Base16 digest]
          )
          mFixed
    parens :: [Text] -> Text
    parens ts = Text.concat ["(", Text.intercalate "," ts, ")"]

    serializeList   :: [Text] -> Text
    serializeList   ls = Text.concat ["[", Text.intercalate "," ls, "]"]

    s = Text.cons '\"' . (`Text.snoc` '\"') . Text.concatMap escape

    escape :: Char -> Text
    escape '\\' = "\\\\"
    escape '\"' = "\\\""
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape c = one c

readDerivation :: (Framed e m, MonadFile m) => FilePath -> m Derivation
readDerivation path = do
  content <- decodeUtf8 <$> readFile path
  either
    (\ err -> throwError $ ErrorCall $ "Failed to parse " <> show path <> ":\n" <> show err)
    pure
    (parse derivationParser path content)

derivationParser :: Parsec () Text Derivation
derivationParser = do
  _ <- "Derive("
  fullOutputs <- serializeList $
    (\[n, p, ht, h] -> (n, p, ht, h)) <$> parens s
  _ <- ","
  inputDrvs   <- Map.fromList <$> serializeList
    (liftA2 (,) ("(" *> s <* ",") (serializeList s <* ")"))
  _ <- ","
  inputSrcs   <- Set.fromList <$> serializeList s
  _ <- ","
  platform    <- s
  _ <- ","
  builder     <- s
  _ <- ","
  args        <- serializeList s
  _ <- ","
  env         <- fmap Map.fromList $ serializeList $ (\[a, b] -> (a, b)) <$> parens s
  _ <- ")"
  eof

  let outputs = Map.fromList $ (\(a, b, _, _) -> (a, b)) <$> fullOutputs
  let (mFixed, hashMode) = parseFixed fullOutputs
  let name = "" -- FIXME (extract from file path ?)
  let useJson = ["__json"] == Map.keys env

  pure $ Derivation {inputs = (inputSrcs, inputDrvs), ..}
 where
  s :: Parsec () Text Text
  s = fmap toText $ string "\"" *> manyTill (escaped <|> regular) (string "\"")
  escaped = char '\\' *>
    (   '\n' <$ string "n"
    <|> '\r' <$ string "r"
    <|> '\t' <$ string "t"
    <|> anySingle
    )
  regular = noneOf ['\\', '"']

  wrap o c p =
    string o *> sepBy p (string ",") <* string c

  parens :: Parsec () Text a -> Parsec () Text [a]
  parens p = wrap "(" ")" p
  serializeList p = wrap "[" "]" p

  parseFixed :: [(Text, Text, Text, Text)] -> (Maybe Store.SomeNamedDigest, HashMode)
  parseFixed fullOutputs = case fullOutputs of
    [("out", _path, rht, hash)] | rht /= "" && hash /= "" ->
      let
        (hashType, hashMode) = case Text.splitOn ":" rht of
          ["r", ht] -> (ht, Recursive)
          [ht] ->      (ht, Flat)
          _ -> error $ "Unsupported hash type for output of fixed-output derivation in .drv file: " <> show fullOutputs
      in
        either
          -- Please, no longer `error show` after migrating to Text
          (\ err -> error $ show $ "Unsupported hash " <> show (hashType <> ":" <> hash) <> "in .drv file: " <> err)
          (\ digest -> (pure digest, hashMode))
          (Store.mkNamedDigest hashType hash)
    _ -> (Nothing, Flat)


defaultDerivationStrict :: forall e t f m b. (MonadNix e t f m, MonadState (b, KeyMap Text) m) => NValue t f m -> m (NValue t f m)
defaultDerivationStrict val = do
    s <- M.mapKeys coerce <$> fromValue @(AttrSet (NValue t f m)) val
    (drv, ctx) <- runWithStringContextT' $ buildDerivationWithContext s
    drvName <- makeStorePathName $ name drv
    let
      inputs = toStorePaths ctx
      ifNotJsonModEnv f =
        bool f id (useJson drv)
          (env drv)

    -- Compute the output paths, and add them to the environment if needed.
    -- Also add the inputs, just computed from the strings contexts.
    drv' <- case mFixed drv of
      Just (Store.SomeDigest digest) -> do
        let
          out = pathToText $ Store.makeFixedOutputPath "/nix/store" (hashMode drv == Recursive) digest drvName
          env' = ifNotJsonModEnv $ Map.insert "out" out
        pure $ drv { inputs, env = env', outputs = one ("out", out) }

      Nothing -> do
        hash <- hashDerivationModulo $ drv
          { inputs
        --, outputs = Map.map (const "") (outputs drv)  -- not needed, this is already the case
          , env =
              ifNotJsonModEnv
                (\ baseEnv ->
                  foldl'
                    (\m k -> Map.insert k "" m)
                    baseEnv
                    (Map.keys $ outputs drv)
                )
          }
        outputs' <- sequence $ Map.mapWithKey (\o _ -> makeOutputPath o hash drvName) $ outputs drv
        pure $ drv
          { inputs
          , outputs = outputs'
          , env = ifNotJsonModEnv (outputs' <>)
          }

    (coerce @Text @VarName -> drvPath) <- pathToText <$> writeDerivation drv'

    -- Memoize here, as it may be our last chance in case of readonly stores.
    drvHash <- Store.encodeDigestWith Store.Base16 <$> hashDerivationModulo drv'
    modify $ second $ MS.insert (coerce drvPath) drvHash

    let
      outputsWithContext =
        Map.mapWithKey
          (\out (coerce -> path) -> makeNixStringWithSingletonContext path $ StringContext drvPath $ DerivationOutput out)
          (outputs drv')
      drvPathWithContext = makeNixStringWithSingletonContext drvPath $ StringContext drvPath AllOutputs
      attrSet = nvStr <$> M.fromList (("drvPath", drvPathWithContext) : Map.toList outputsWithContext)
    -- TODO: Add location information for all the entries.
    --              here --v
    pure $ nvSet mempty (M.mapKeys coerce attrSet)

  where

    pathToText = decodeUtf8 . Store.storePathToRawFilePath

    makeOutputPath o h n = do
      name <- makeStorePathName $ Store.unStorePathName n <> if o == "out" then "" else "-" <> o
      pure $ pathToText $ Store.makeStorePath "/nix/store" ("output:" <> encodeUtf8 o) h name

    toStorePaths :: HashSet StringContext -> (Set Text, Map Text [Text])
    toStorePaths ctx = foldl (flip addToInputs) (mempty, mempty) ctx

    addToInputs :: Bifunctor p => StringContext -> p (Set Text) (Map Text [Text])  -> p (Set Text) (Map Text [Text])
    addToInputs (StringContext path kind) = case kind of
      DirectPath -> first (Set.insert (coerce path))
      DerivationOutput o -> second (Map.insertWith (<>) (coerce path) [o])
      AllOutputs ->
        -- TODO: recursive lookup. See prim_derivationStrict
        -- XXX: When is this really used ?
        error "Not implemented: derivations depending on a .drv file are not yet supported."


-- | Build a derivation in a context collecting string contexts.
-- This is complex from a typing standpoint, but it allows to perform the
-- full computation without worrying too much about all the string's contexts.
buildDerivationWithContext :: forall e t f m. (MonadNix e t f m) => KeyMap (NValue t f m) -> WithStringContextT m Derivation
buildDerivationWithContext drvAttrs = do
    -- Parse name first, so we can add an informative frame
    drvName     <- getAttr   "name"                      $ assertDrvStoreName <=< extractNixString
    withFrame' Info (ErrorCall $ "While evaluating derivation " <> show drvName) $ do

      useJson     <- getAttrOr "__structuredAttrs" False     pure
      ignoreNulls <- getAttrOr "__ignoreNulls"     False     pure

      args        <- getAttrOr "args"              mempty  $ traverse (extractNixString <=< fromValue')
      builder     <- getAttr   "builder"                     extractNixString
      platform    <- getAttr   "system"                    $ assertNonNull <=< extractNoCtx
      mHash       <- getAttrOr "outputHash"        mempty  $ (pure . pure) <=< extractNoCtx
      hashMode    <- getAttrOr "outputHashMode"    Flat    $ parseHashMode <=< extractNoCtx
      outputs     <- getAttrOr "outputs"           ["out"] $ traverse (extractNoCtx <=< fromValue')

      mFixedOutput <-
        maybe
          (pure Nothing)
          (\ hash -> do
            when (outputs /= ["out"]) $ lift $ throwError $ ErrorCall "Multiple outputs are not supported for fixed-output derivations"
            hashType <- getAttr "outputHashAlgo" extractNoCtx
            digest <- lift $ either (throwError . ErrorCall) pure $ Store.mkNamedDigest hashType hash
            pure $ pure digest)
          mHash

      -- filter out null values if needed.
      attrs <-
        lift $
          bool
            (pure drvAttrs)
            (M.mapMaybe id <$>
              traverse
                (fmap
                  (\case
                    NVConstant NNull -> Nothing
                    _value           -> Just _value
                  )
                  . demand
                )
                drvAttrs
            )
            ignoreNulls

      env <- if useJson
        then do
          jsonString :: NixString <- lift $ nvalueToJSONNixString $ nvSet mempty $ M.mapKeys coerce $
            deleteKeys [ "args", "__ignoreNulls", "__structuredAttrs" ] attrs
          rawString :: Text <- extractNixString jsonString
          pure $ one ("__json", rawString)
        else
          traverse (extractNixString <=< lift . coerceToString callFunc CopyToStore CoerceAny) $
            Map.fromList $ M.toList $ deleteKeys [ "args", "__ignoreNulls" ] attrs

      pure $ Derivation { platform, builder, args, env,  hashMode, useJson
        , name = drvName
        , outputs = Map.fromList $ (, mempty) <$> outputs
        , mFixed = mFixedOutput
        , inputs = (mempty, mempty) -- stub for now
        }
  where

    -- common functions, lifted to WithStringContextT

    fromValue' :: (FromValue a m (NValue' t f m (NValue t f m)), MonadNix e t f m) => NValue t f m -> WithStringContextT m a
    fromValue' = lift . fromValue

    withFrame' :: (Framed e m, Exception s) => NixLevel -> s -> WithStringContextT m a -> WithStringContextT m a
    withFrame' level f = join . lift . withFrame level f . pure

    -- shortcuts to get the (forced) value of an KeyMap field

    getAttrOr' :: forall v a. (MonadNix e t f m, FromValue v m (NValue' t f m (NValue t f m)))
      => Text -> m a -> (v -> WithStringContextT m a) -> WithStringContextT m a
    getAttrOr' n d f = case M.lookup n drvAttrs of
      Nothing -> lift d
      Just v  -> withFrame' Info (ErrorCall $ "While evaluating attribute '" <> show n <> "'") $
                   f =<< fromValue' v

    getAttrOr n d f = getAttrOr' n (pure d) f

    getAttr n = getAttrOr' n (throwError $ ErrorCall $ "Required attribute '" <> show n <> "' not found.")

    -- Test validity for fields

    assertDrvStoreName :: MonadNix e t f m => Text -> WithStringContextT m Text
    assertDrvStoreName name = lift $ do
      let invalid c = not $ isAscii c && (isAlphaNum c || c `elem` ("+-._?=" :: String)) -- isAlphaNum allows non-ascii chars.
      let failWith reason = throwError $ ErrorCall $ "Store name " <> show name <> " " <> reason
      when ("." `Text.isPrefixOf` name)    $ failWith "cannot start with a period"
      when (Text.length name > 211)        $ failWith "must be no longer than 211 characters"
      when (Text.any invalid name)         $ failWith "contains some invalid character"
      when (".drv" `Text.isSuffixOf` name) $ failWith "is not allowed to end in '.drv'"
      pure name

    extractNoCtx :: MonadNix e t f m => NixString -> WithStringContextT m Text
    extractNoCtx ns =
      maybe
        (lift $ throwError $ ErrorCall $ "The string " <> show ns <> " is not allowed to have a context.")
        pure
        (getStringNoContext ns)

    assertNonNull :: MonadNix e t f m => Text -> WithStringContextT m Text
    assertNonNull t = do
      when (Text.null t) $ lift $ throwError $ ErrorCall "Value must not be empty"
      pure t

    parseHashMode :: MonadNix e t f m => Text -> WithStringContextT m HashMode
    parseHashMode = \case
      "flat" ->      pure Flat
      "recursive" -> pure Recursive
      other -> lift $ throwError $ ErrorCall $ "Hash mode " <> show other <> " is not valid. It must be either 'flat' or 'recursive'"

    -- Other helpers

    deleteKeys :: [Text] -> KeyMap a -> KeyMap a
    deleteKeys keys attrSet = foldl' (flip M.delete) attrSet keys

