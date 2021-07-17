{-# LANGUAGE StrictData #-}

-- | Definitions & defaults for the CLI options
module Nix.Options where

import           Data.Time

--  2021-07-15: NOTE: What these are? They need to be documented.
-- Also need better names. Foe example, Maybes & lists names need to show their type in the name.
data Options = Options
    { verbose      :: Verbosity
    , tracing      :: Bool
    , thunks       :: Bool
    , values       :: Bool
    , showScopes   :: Bool
    , reduce       :: Maybe FilePath
    , reduceSets   :: Bool
    , reduceLists  :: Bool
    , parse        :: Bool
    , parseOnly    :: Bool
    , finder       :: Bool
    , findFile     :: Maybe FilePath
    , strict       :: Bool
    , evaluate     :: Bool
    , json         :: Bool
    , xml          :: Bool
    , attr         :: Maybe Text
    , include      :: [FilePath]
    , check        :: Bool
    , readFrom     :: Maybe FilePath
    , cache        :: Bool
    , repl         :: Bool
    , ignoreErrors :: Bool
    , expression   :: Maybe Text
    , arg          :: [(Text, Text)]
    , argstr       :: [(Text, Text)]
    , fromFile     :: Maybe FilePath
    , currentTime  :: UTCTime
    , filePaths    :: [FilePath]
    }
    deriving Show

defaultOptions :: UTCTime -> Options
defaultOptions current = Options { verbose      = ErrorsOnly
                                 , tracing      = False
                                 , thunks       = False
                                 , values       = False
                                 , showScopes   = False
                                 , reduce       = mempty
                                 , reduceSets   = False
                                 , reduceLists  = False
                                 , parse        = False
                                 , parseOnly    = False
                                 , finder       = False
                                 , findFile     = mempty
                                 , strict       = False
                                 , evaluate     = False
                                 , json         = False
                                 , xml          = False
                                 , attr         = mempty
                                 , include      = mempty
                                 , check        = False
                                 , readFrom     = mempty
                                 , cache        = False
                                 , repl         = False
                                 , ignoreErrors = False
                                 , expression   = mempty
                                 , arg          = mempty
                                 , argstr       = mempty
                                 , fromFile     = mempty
                                 , currentTime  = current
                                 , filePaths    = mempty
                                 }

data Verbosity
    = ErrorsOnly
    | Informational
    | Talkative
    | Chatty
    | DebugInfo
    | Vomit
    deriving (Eq, Ord, Enum, Bounded, Show)
