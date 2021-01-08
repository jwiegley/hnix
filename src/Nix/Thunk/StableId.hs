{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE MagicHash #-}

-- Equivalent to [Int], but with near-O(1) amortized comparison
module Nix.Thunk.StableId (StableId, nil, cons, uncons) where

import Data.IORef
import System.IO.Unsafe
import GHC.Prim
import Data.Hashable
import Data.List (unfoldr)
import Data.Ord

--TODO: If we have a really long chain, we will keep leaking memory; what can we do about this?

data StableId = StableId
  { _stableId_value :: {-# UNPACK #-} !Int
  , _stableId_hash :: {-# UNPACK #-} !Int
  , _stableId_parent :: {-# UNPACK #-} !(IORef StableId)
  }

{-# NOINLINE nil #-} -- If nil is not a single value on the heap, infinite recursion can result
nil :: StableId
nil = StableId 0 0 $ unsafePerformIO $ newIORef $ error "nil"

cons :: Int -> StableId -> StableId
cons v p@(StableId _ ph _) = StableId v (hash (v, ph)) $ unsafeDupablePerformIO $ newIORef p

uncons :: StableId -> Maybe (Int, StableId)
uncons s = if _stableId_parent s == _stableId_parent nil
  then Nothing
  else Just
  ( _stableId_value s
  , unsafeDupablePerformIO $ readIORef $ _stableId_parent s
  )

--TODO: Reimplement Eq in terms of Ord?
instance Eq StableId where
  a == b = if
    | _stableId_parent a == _stableId_parent b -- We're the exact same heap object
      -> True
    | _stableId_hash a /= _stableId_hash b || _stableId_value a /= _stableId_value b -- We're definitely different
      -> False
    | otherwise -- Different objects, but same value and hash.  These are either the same value or a hash collision.
      -> unsafeDupablePerformIO $ do
           pa <- readIORef $ _stableId_parent a
           pb <- readIORef $ _stableId_parent b
           case reallyUnsafePtrEquality# pa pb of
             -- Parents are different objects
             0# -> if pa == pb
               then do writeIORef (_stableId_parent b) pa -- Parents are equivalent, so unify
                       return True
               else return False -- Parents are not equivalent, so leave them alone
             -- Parents are the same object already
             _ -> return True

instance Ord StableId where
  a `compare` b = case comparing _stableId_hash a b <> comparing _stableId_value a b of
    LT -> LT
    GT -> GT
    EQ -> case _stableId_parent a == _stableId_parent b of
      True -> EQ
      False -> unsafeDupablePerformIO $ do
        pa <- readIORef $ _stableId_parent a
        pb <- readIORef $ _stableId_parent b
        case reallyUnsafePtrEquality# pa pb of
          -- Parents are different objects
          0# -> case pa `compare` pb of
            LT -> return LT
            GT -> return GT
            EQ -> do
              writeIORef (_stableId_parent b) pa
              return EQ
          -- Parents are the same object already
          _ -> return EQ

toList :: StableId -> [Int]
toList = unfoldr uncons

instance Show StableId where
  showsPrec n = showsPrec n . toList
