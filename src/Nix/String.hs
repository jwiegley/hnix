{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Nix.String
  ( NixString
  , getContext
  , makeNixString
  , StringContext(..)
  , ContextFlavor(..)
  , NixLikeContext(..)
  , NixLikeContextValue(..)
  , toNixLikeContext
  , fromNixLikeContext
  , stringHasContext
  , intercalateNixString
  , getStringNoContext
  , stringIgnoreContext
  , makeNixStringWithoutContext
  , makeNixStringWithSingletonContext
  , modifyNixContents
  , WithStringContext
  , WithStringContextT(..)
  , extractNixString
  , addStringContext
  , addSingletonStringContext
  , runWithStringContextT
  , runWithStringContextT'
  , runWithStringContext
  , runWithStringContext'
  )
where




import           Nix.Utils
import           Control.Monad.Writer           ( WriterT(..), MonadWriter(tell))
import qualified Data.HashMap.Lazy             as M
import qualified Data.HashSet                  as S
import qualified Data.Text                     as Text
import           Nix.Expr.Types                 ( VarName(..)
                                                , AttrSet
                                                )


-- * Types

-- ** Context

-- | A Nix 'StringContext' ...
data StringContext =
  StringContext
    { scPath :: !VarName
    , scFlavor :: !ContextFlavor
    }
  deriving (Eq, Ord, Show, Generic)

instance Hashable StringContext

-- | A 'ContextFlavor' describes the sum of possible derivations for string contexts
data ContextFlavor
  = DirectPath
  | AllOutputs
  | DerivationOutput !Text
  deriving (Show, Eq, Ord, Generic)

instance Hashable ContextFlavor

newtype NixLikeContext =
  NixLikeContext
    { getNixLikeContext :: AttrSet NixLikeContextValue
    }
  deriving (Eq, Ord, Show, Generic)

data NixLikeContextValue =
  NixLikeContextValue
    { nlcvPath :: !Bool
    , nlcvAllOutputs :: !Bool
    , nlcvOutputs :: ![Text]
    }
  deriving (Show, Eq, Ord, Generic)

instance Semigroup NixLikeContextValue where
  a <> b =
    NixLikeContextValue
      { nlcvPath       = nlcvPath       a || nlcvPath       b
      , nlcvAllOutputs = nlcvAllOutputs a || nlcvAllOutputs b
      , nlcvOutputs    = nlcvOutputs    a <> nlcvOutputs    b
      }

instance Monoid NixLikeContextValue where
  mempty = NixLikeContextValue False False mempty


-- ** StringContext accumulator

-- | A monad for accumulating string context while producing a result string.
newtype WithStringContextT m a =
  WithStringContextT
    (WriterT (S.HashSet StringContext) m a )
  deriving (Functor, Applicative, Monad, MonadTrans, MonadWriter (S.HashSet StringContext))

type WithStringContext = WithStringContextT Identity


-- ** NixString

data NixString =
  NixString
    { nsContents :: !Text
    , nsContext :: !(S.HashSet StringContext)
    }
  deriving (Eq, Ord, Show, Generic)

instance Semigroup NixString where
  NixString s1 t1 <> NixString s2 t2 = NixString (s1 <> s2) (t1 <> t2)

instance Monoid NixString where
 mempty = NixString mempty mempty

instance Hashable NixString


-- * Functions

-- ** Makers

-- | Constructs NixString without a context
makeNixStringWithoutContext :: Text -> NixString
makeNixStringWithoutContext = (`NixString` mempty)

-- | Create NixString using a singleton context
makeNixStringWithSingletonContext
  :: VarName -> StringContext -> NixString
makeNixStringWithSingletonContext s c = NixString (coerce @VarName @Text s) $ one c

-- | Create NixString from a Text and context
makeNixString :: Text -> S.HashSet StringContext -> NixString
makeNixString = NixString


-- ** Checkers

-- | Returns True if the NixString has an associated context
stringHasContext :: NixString -> Bool
stringHasContext (NixString _ c) = not $ null c


-- ** Getters

getContext :: NixString -> S.HashSet StringContext
getContext = nsContext

fromNixLikeContext :: NixLikeContext -> S.HashSet StringContext
fromNixLikeContext =
  S.fromList . (toStringContexts <=< (M.toList . getNixLikeContext))

-- | Extract the string contents from a NixString that has no context
getStringNoContext :: NixString -> Maybe Text
getStringNoContext (NixString s c)
  | null c    = pure s
  | otherwise = mempty

-- | Extract the string contents from a NixString even if the NixString has an associated context
stringIgnoreContext :: NixString -> Text
stringIgnoreContext (NixString s _) = s

-- | Get the contents of a 'NixString' and write its context into the resulting set.
extractNixString :: Monad m => NixString -> WithStringContextT m Text
extractNixString (NixString s c) =
  WithStringContextT $
    s <$ tell c


-- ** Setters

-- this really should be 2 args, then with @toStringContexts path@ laziness it would tail recurse.
-- for now tuple dissected internaly with laziness preservation.
toStringContexts :: (VarName, NixLikeContextValue) -> [StringContext]
toStringContexts ~(path, nlcv) =
  go nlcv
 where

  go cv =
    case cv of
      NixLikeContextValue True _    _ ->
        mkLstCtxFor DirectPath cv { nlcvPath = False }
      NixLikeContextValue _    True _ ->
        mkLstCtxFor AllOutputs cv { nlcvAllOutputs = False }
      NixLikeContextValue _    _    ls | not (null ls) ->
        mkCtxFor . DerivationOutput <$> ls
      _ -> mempty
   where
    mkCtxFor = StringContext path
    mkLstCtxFor t c = mkCtxFor t : go c

toNixLikeContextValue :: StringContext -> (VarName, NixLikeContextValue)
toNixLikeContextValue sc =
  ( scPath sc
  , case scFlavor sc of
      DirectPath         -> NixLikeContextValue True False mempty
      AllOutputs         -> NixLikeContextValue False True mempty
      DerivationOutput t -> NixLikeContextValue False False [t]
  )

toNixLikeContext :: S.HashSet StringContext -> NixLikeContext
toNixLikeContext stringContext =
  NixLikeContext $
    S.foldr
      go
      mempty
      stringContext
 where
  go sc hm =
    let (t, nlcv) = toNixLikeContextValue sc in
    M.insertWith (<>) t nlcv hm

-- | Add 'StringContext's into the resulting set.
addStringContext
  :: Monad m => S.HashSet StringContext -> WithStringContextT m ()
addStringContext = WithStringContextT . tell

-- | Add a 'StringContext' into the resulting set.
addSingletonStringContext :: Monad m => StringContext -> WithStringContextT m ()
addSingletonStringContext = WithStringContextT . tell . one

-- | Run an action producing a string with a context and put those into a 'NixString'.
runWithStringContextT :: Monad m => WithStringContextT m Text -> m NixString
runWithStringContextT (WithStringContextT m) =
  uncurry NixString <$> runWriterT m

-- | Run an action producing a string with a context and put those into a 'NixString'.
runWithStringContext :: WithStringContextT Identity Text -> NixString
runWithStringContext = runIdentity . runWithStringContextT


-- ** Modifiers

-- | Modify the string part of the NixString, leaving the context unchanged
modifyNixContents :: (Text -> Text) -> NixString -> NixString
modifyNixContents f (NixString s c) = NixString (f s) c

-- | Run an action that manipulates nix strings, and collect the contexts encountered.
-- Warning: this may be unsafe, depending on how you handle the resulting context list.
runWithStringContextT' :: Monad m => WithStringContextT m a -> m (a, S.HashSet StringContext)
runWithStringContextT' (WithStringContextT m) = runWriterT m

-- | Run an action that manipulates nix strings, and collect the contexts encountered.
-- Warning: this may be unsafe, depending on how you handle the resulting context list.
runWithStringContext' :: WithStringContextT Identity a -> (a, S.HashSet StringContext)
runWithStringContext' = runIdentity . runWithStringContextT'

-- | Combine NixStrings with a separator
intercalateNixString :: NixString -> [NixString] -> NixString
intercalateNixString _   []   = mempty
intercalateNixString _   [ns] = ns
intercalateNixString sep nss  =
  uncurry NixString $ mapPair intertwine unpackNss
 where

  intertwine =
    ( Text.intercalate (nsContents sep)
    , S.unions . (:)   (nsContext  sep)
    )

  unpackNss = (fnss nsContents, fnss nsContext)
   where
    fnss = (`fmap` nss) -- do once

