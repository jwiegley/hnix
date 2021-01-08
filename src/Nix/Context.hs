{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Nix.Context where

import           Nix.Options
import           Nix.Frames
import           Nix.Utils
import           Nix.Expr.Types.Annotated       ( SrcSpan
                                                , nullSpan
                                                )

data Context = Context
    { source  :: SrcSpan -- Should we capture?
    , frames  :: Frames -- Don't capture (should change)
    , options :: Options -- Don't capture (never changes)
    }


instance Has Context SrcSpan where
  hasLens f a = (\x -> a { source = x }) <$> f (source a)

instance Has Context Frames where
  hasLens f a = (\x -> a { frames = x }) <$> f (frames a)

instance Has Context Options where
  hasLens f a = (\x -> a { options = x }) <$> f (options a)

newContext :: Options -> Context
newContext = Context nullSpan []
