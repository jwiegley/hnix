{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}

module Nix.Render where

import           Prelude                 hiding ( readFile )

import qualified Data.ByteString               as BS
import qualified Data.Set                      as Set
import           Nix.Utils.Fix1                 ( Fix1T
                                                , MonadFix1T )
import           Nix.Expr.Types.Annotated
import           Prettyprinter
import qualified System.Directory              as S
import qualified System.Posix.Files            as S
import           Text.Megaparsec.Error
import           Text.Megaparsec.Pos
import qualified Data.Text                     as Text

class MonadFail m => MonadFile m where
    readFile :: FilePath -> m ByteString
    default readFile :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m ByteString
    readFile = lift . readFile
    listDirectory :: FilePath -> m [FilePath]
    default listDirectory :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m [FilePath]
    listDirectory = lift . listDirectory
    getCurrentDirectory :: m FilePath
    default getCurrentDirectory :: (MonadTrans t, MonadFile m', m ~ t m') => m FilePath
    getCurrentDirectory = lift getCurrentDirectory
    canonicalizePath :: FilePath -> m FilePath
    default canonicalizePath :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m FilePath
    canonicalizePath = lift . canonicalizePath
    getHomeDirectory :: m FilePath
    default getHomeDirectory :: (MonadTrans t, MonadFile m', m ~ t m') => m FilePath
    getHomeDirectory = lift getHomeDirectory
    doesPathExist :: FilePath -> m Bool
    default doesPathExist :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m Bool
    doesPathExist = lift . doesPathExist
    doesFileExist :: FilePath -> m Bool
    default doesFileExist :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m Bool
    doesFileExist = lift . doesFileExist
    doesDirectoryExist :: FilePath -> m Bool
    default doesDirectoryExist :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m Bool
    doesDirectoryExist = lift . doesDirectoryExist
    getSymbolicLinkStatus :: FilePath -> m S.FileStatus
    default getSymbolicLinkStatus :: (MonadTrans t, MonadFile m', m ~ t m') => FilePath -> m S.FileStatus
    getSymbolicLinkStatus = lift . getSymbolicLinkStatus

instance MonadFile IO where
  readFile              = BS.readFile
  listDirectory         = S.listDirectory
  getCurrentDirectory   = S.getCurrentDirectory
  canonicalizePath      = S.canonicalizePath
  getHomeDirectory      = S.getHomeDirectory
  doesPathExist         = S.doesPathExist
  doesFileExist         = S.doesFileExist
  doesDirectoryExist    = S.doesDirectoryExist
  getSymbolicLinkStatus = S.getSymbolicLinkStatus


instance (MonadFix1T t m, MonadFail (Fix1T t m), MonadFile m) => MonadFile (Fix1T t m)

posAndMsg :: SourcePos -> Doc a -> ParseError s Void
posAndMsg (SourcePos _ lineNo _) msg =
  FancyError
    (unPos lineNo)
    (Set.fromList [ErrorFail (show msg) :: ErrorFancy Void])

renderLocation :: MonadFile m => SrcSpan -> Doc a -> m (Doc a)
renderLocation (SrcSpan (SourcePos file begLine begCol) (SourcePos file' endLine endCol)) msg
  | file == file' && file == "<string>" && begLine == endLine
  = pure $ "In raw input string at position " <> pretty (unPos begCol)

  | file /= "<string>" && file == file'
  = do
    exist <- doesFileExist file
    if exist
      then do
        txt <- sourceContext file begLine begCol endLine endCol msg
        pure $
          vsep
            [ "In file " <> errorContext file begLine begCol endLine endCol <> ":"
            , txt
            ]
      else pure msg
renderLocation (SrcSpan beg end) msg = fail $ "Don't know how to render range from " <> show beg <>" to " <> show end <>" for fail: " <> show msg

errorContext :: FilePath -> Pos -> Pos -> Pos -> Pos -> Doc a
errorContext path bl bc _el _ec =
  pretty path <> ":" <> pretty (unPos bl) <> ":" <> pretty (unPos bc)

sourceContext
  :: MonadFile m => FilePath -> Pos -> Pos -> Pos -> Pos -> Doc a -> m (Doc a)
sourceContext path (unPos -> begLine) (unPos -> _begCol) (unPos -> endLine) (unPos -> _endCol) msg
  = do
    let beg' = max 1 $ begLine - 3
        end' =         endLine + 3
    ls <-
      fmap pretty
      .   take (end' - beg')
      .   drop (pred beg')
      .   lines
      .   decodeUtf8
      <$> readFile path
    let
      longest = Text.length $ show $ beg' + length ls - 1
      pad :: Int -> Text
      pad n =
        let
          ns :: Text
          ns = show n
          nsp = Text.replicate (longest - Text.length ns) " " <> ns
        in
          if
          | n == begLine && n == endLine -> "==> " <> nsp <> " |  "
          | n >= begLine && n <= endLine -> "  > " <> nsp <> " |  "
          | otherwise                    -> "    " <> nsp <> " |  "
      composeLine n l =
        [pretty (pad n) <> l]
        <> bool mempty
          [ pretty $
              Text.replicate (Text.length (pad n) - 3) " "
              <> "|"
              <> Text.replicate (_begCol + 1) " "
              <> Text.replicate (_endCol - _begCol) "^"
          ]
          (begLine == endLine && n == endLine)
        -- XXX: Consider inserting the message here when it is small enough.
        -- ATM some messages are so huge that they take prevalence over the source listing.
        -- ++ [ indent (length $ pad n) msg | n == endLine ]

      ls' = concat $ zipWith composeLine [beg' ..] ls

    pure $ vsep $ ls' <> [ indent (Text.length $ pad begLine) msg ]
