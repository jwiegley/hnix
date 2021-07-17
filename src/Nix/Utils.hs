{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Nix.Utils (module Nix.Utils, module X) where

import           Control.Monad.Fix              ( MonadFix(..) )
import           Control.Monad.Free             ( Free(..) )
import           Control.Monad.Trans.Control    ( MonadTransControl(..) )
import qualified Data.Aeson                    as A
import qualified Data.Aeson.Encoding           as A
import           Data.Fix                       ( Fix(..) )
import qualified Data.HashMap.Lazy             as M
import qualified Data.Text                     as Text
import qualified Data.Vector                   as V
import           Lens.Family2                  as X hiding ((&))
import           Lens.Family2.Stock             ( _1
                                                , _2
                                                )
import           Lens.Family2.TH                ( makeLensesBy )

#if ENABLE_TRACING
import           Debug.Trace as X
#else
-- Well, since it is currently CPP intermingled with Debug.Trace, required to use String here.
trace :: String -> a -> a
trace = const id
{-# inline trace #-}
traceM :: Monad m => String -> m ()
traceM = const pass
{-# inline traceM #-}
#endif

$(makeLensesBy (\n -> pure $ "_" <> n) ''Fix)

-- | > Hashmap Text -- type synonym
type KeyMap = HashMap Text

-- | F-algebra defines how to reduce the fixed-point of a functor to a value.
-- > type Alg f a = f a -> a
type Alg f a = f a -> a

-- | > type AlgM f m a = f a -> m a
type AlgM f m a = f a -> m a

-- | Do according transformation.
--
-- It is a transformation of a recursion scheme.
-- See @TransformF@.
type Transform f a = TransformF (Fix f) a
-- | Do according transformation.
--
-- It is a transformation between functors.
-- ...
-- You got me, it is a natural transformation.
type TransformF f a = (f -> a) -> f -> a

loeb :: Functor f => f (f a -> a) -> f a
loeb x = go
 where
  go = ($ go) <$> x

loebM :: (MonadFix m, Traversable t) => t (t a -> m a) -> m (t a)
-- Sectioning here insures optimization happening.
loebM f = mfix $ \a -> (`traverse` f) ($ a)
{-# inline loebM #-}

para :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = f . fmap (id &&& para f) . unFix

paraM :: (Traversable f, Monad m) => (f (Fix f, a) -> m a) -> Fix f -> m a
paraM f = f <=< traverse (\x -> (x, ) <$> paraM f x) . unFix

cataP :: Functor f => (Fix f -> f a -> a) -> Fix f -> a
cataP f x = f x . fmap (cataP f) . unFix $ x

cataPM :: (Traversable f, Monad m) => (Fix f -> f a -> m a) -> Fix f -> m a
cataPM f x = f x <=< traverse (cataPM f) . unFix $ x

lifted
  :: (MonadTransControl u, Monad (u m), Monad m)
  => ((a -> m (StT u b)) -> m (StT u b))
  -> (a -> u m b)
  -> u m b
lifted f k =
  do
    lftd <- liftWith (\run -> f (run . k))
    restoreT $ pure lftd

-- | Replace:
--  @Pure a -> a@
--  @Free -> Fix@
freeToFix :: Functor f => (a -> Fix f) -> Free f a -> Fix f
freeToFix f = go
 where
  go =
    free
      f
      $ Fix . (go <$>)

-- | Replace:
--  @a -> Pure a@
--  @Fix -> Free@
fixToFree :: Functor f => Fix f -> Free f a
fixToFree = Free . go
 where
  go (Fix f) = Free . go <$> f

-- | adi is Abstracting Definitional Interpreters:
--
--     https://arxiv.org/abs/1707.04755
--
--   Essentially, it does for evaluation what recursion schemes do for
--   representation: allows threading layers through existing structure, only
--   in this case through behavior.
adi
  :: Functor f
  => Transform f a
  -> Alg f a
  -> Fix f
  -> a
adi g f = g $ f . (adi g f <$>) . unFix

adiM
  :: ( Traversable t
     , Monad m
     )
  => Transform t (m a)
  -> AlgM t m a
  -> Fix t
  -> m a
adiM g f = g $ f <=< traverse (adiM g f) . unFix


class Has a b where
  hasLens :: Lens' a b

instance Has a a where
  hasLens f = f

instance Has (a, b) a where
  hasLens = _1

instance Has (a, b) b where
  hasLens = _2

toEncodingSorted :: A.Value -> A.Encoding
toEncodingSorted = \case
  A.Object m ->
    A.pairs
      . mconcat
      . ((\(k, v) -> A.pair k $ toEncodingSorted v) <$>)
      . sortWith fst
      $ M.toList m
  A.Array l -> A.list toEncodingSorted $ V.toList l
  v         -> A.toEncoding v

data NixPathEntryType = PathEntryPath | PathEntryURI deriving (Show, Eq)

-- | @NIX_PATH@ is colon-separated, but can also contain URLs, which have a colon
-- (i.e. @https://...@)
uriAwareSplit :: Text -> [(Text, NixPathEntryType)]
uriAwareSplit txt =
  case Text.break (== ':') txt of
    (e1, e2)
      | Text.null e2                              -> [(e1, PathEntryPath)]
      | "://" `Text.isPrefixOf` e2      ->
        let ((suffix, _) : path) = uriAwareSplit (Text.drop 3 e2) in
        (e1 <> "://" <> suffix, PathEntryURI) : path
      | otherwise                                 -> (e1, PathEntryPath) : uriAwareSplit (Text.drop 1 e2)

-- | Analog for @bool@ or @maybe@, for list-like cons structures.
list
  :: Foldable t
  => b -> (t a -> b) -> t a -> b
list e f l =
  bool
    (f l)
    e
    (null l)
{-# inline list #-}

whenText
  :: a -> (Text -> a) -> Text -> a
whenText e f t =
  bool
    (f t)
    e
    (Text.null t)

-- | Lambda analog of @maybe@ or @either@ for Free monad.
free :: (a -> b) -> (f (Free f a) -> b) -> Free f a -> b
free fP fF fr =
  case fr of
    Pure a -> fP a
    Free fa -> fF fa
{-# inline free #-}


whenTrue :: (Monoid a)
  => a -> Bool -> a
whenTrue =
  bool
    mempty
{-# inline whenTrue #-}

whenFalse :: (Monoid a)
  => a  -> Bool  -> a
whenFalse f =
  bool
    f
    mempty
{-# inline whenFalse #-}

whenFree :: (Monoid b)
  => (f (Free f a) -> b) -> Free f a -> b
whenFree =
  free
    mempty
{-# inline whenFree #-}

whenPure :: (Monoid b)
  => (a -> b) -> Free f a -> b
whenPure f =
  free
    f
    mempty
{-# inline whenPure #-}


-- | Apply a single function to both components of a pair.
--
-- > both succ (1,2) == (2,3)
--
-- Taken From package @extra@
both :: (a -> b) -> (a, a) -> (b, b)
both f (x,y) = (f x, f y)
{-# inline both #-}


-- | Duplicates object into a tuple.
dup :: a -> (a, a)
dup x = (x, x)
{-# inline dup #-}

-- | From @utility-ht@ for tuple laziness.
mapPair :: (a -> c, b -> d) -> (a,b) -> (c,d)
mapPair ~(f,g) ~(a,b) = (f a, g b)
{-# inline mapPair #-}

-- After migration from the @relude@ - @relude: pass -> stub@
-- | @pure mempty@: Short-curcuit, stub.
stub :: (Applicative f, Monoid a) => f a
stub = pure mempty
{-# inline stub #-}
