{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}

-- | The source location annotated nix expression type and supporting types.
--
module Nix.Expr.Types.Annotated
  ( module Nix.Expr.Types.Annotated
  , module Data.Functor.Compose
  , SourcePos(..)
  , unPos
  , mkPos
  )
where

import           Codec.Serialise
import           Control.DeepSeq
import           Data.Aeson                     ( ToJSON(..)
                                                , FromJSON(..)
                                                )
import           Data.Aeson.TH
import           Data.Binary                    ( Binary(..) )
import           Data.Data
import           Data.Eq.Deriving
import           Data.Fix                       ( Fix(..)
                                                , unfoldFix )
import           Data.Functor.Compose
import           Data.Hashable.Lifted
import           Data.Ord.Deriving
import           GHC.Generics
import           Nix.Atoms
import           Nix.Expr.Types
import           Text.Megaparsec                ( unPos
                                                , mkPos
                                                )
import           Text.Megaparsec.Pos            ( SourcePos(..) )
import           Text.Read.Deriving
import           Text.Show.Deriving

-- * data type @SrcSpan@ - a zone in a source file

-- | Demarcation of a chunk in a source file.
data SrcSpan = SrcSpan
    { spanBegin :: SourcePos
    , spanEnd   :: SourcePos
    }
    deriving (Ord, Eq, Generic, Typeable, Data, Show, NFData, Hashable)

-- ** Instances

instance Semigroup SrcSpan where
  s1 <> s2 =
    SrcSpan
      ((min `on` spanBegin) s1 s2)
      ((max `on` spanEnd  ) s1 s2)

instance Binary SrcSpan
instance ToJSON SrcSpan
instance FromJSON SrcSpan

instance Serialise SrcSpan

-- * data type @Ann@

-- | A type constructor applied to a type along with an annotation
--
-- Intended to be used with 'Fix':
-- @type MyType = Fix (Compose (Ann Annotation) F)@
data Ann ann a = Ann
    { annotation :: ann
    , annotated  :: a
    }
    deriving (Ord, Eq, Data, Generic, Generic1, Typeable, Functor, Foldable,
              Traversable, Read, Show, NFData, Hashable)

type AnnF ann f = Compose (Ann ann) f

-- | Pattern: @(Compose (Ann _ _))@.
pattern AnnFP
  :: ann
  -> f a
  -> Compose (Ann ann) f a
pattern AnnFP ann f = Compose (Ann ann f)
{-# complete AnnFP #-}

-- | Pattern: @Fix (Compose (Ann _ _))@.
-- Fix composes units of (annotations & the annotated) into one object.
-- Giving annotated expression.
pattern AnnE
  :: forall ann (f :: Type -> Type)
  . ann
  -> f (Fix (AnnF ann f))
  -> Fix (AnnF ann f)
pattern AnnE ann a = Fix (AnnFP ann a)
{-# complete AnnE #-}

annToAnnF :: Ann ann (f (Fix (AnnF ann f))) -> Fix (AnnF ann f)
annToAnnF (Ann ann a) = AnnE ann a

-- ** Instances

instance Hashable ann => Hashable1 (Ann ann)

instance NFData ann => NFData1 (Ann ann)

instance (Binary ann, Binary a) => Binary (Ann ann a)

$(deriveEq1   ''Ann)
$(deriveEq2   ''Ann)
$(deriveOrd1  ''Ann)
$(deriveOrd2  ''Ann)
$(deriveRead1 ''Ann)
$(deriveRead2 ''Ann)
$(deriveShow1 ''Ann)
$(deriveShow2 ''Ann)
$(deriveJSON1 defaultOptions ''Ann)
$(deriveJSON2 defaultOptions ''Ann)

instance (Serialise ann, Serialise a) => Serialise (Ann ann a)

-- ** @NExprLoc{,F}@ - annotated Nix expression

type NExprLocF = AnnF SrcSpan NExprF

instance Serialise r => Serialise (NExprLocF r) where
  encode (AnnFP ann a) = encode ann <> encode a
  decode =
    liftA2 AnnFP
      decode
      decode

instance Binary r => Binary (NExprLocF r)

-- | Annotated Nix expression (each subexpression direct to its source location).
type NExprLoc = Fix NExprLocF

instance Serialise NExprLoc

instance Binary NExprLoc

-- * Other

stripAnnotation :: Functor f => Fix (AnnF ann f) -> Fix f
stripAnnotation = unfoldFix (stripAnn . unFix)

stripAnn :: AnnF ann f r -> f r
stripAnn = annotated . getCompose

nUnary :: Ann SrcSpan NUnaryOp -> NExprLoc -> NExprLoc
nUnary (Ann s1 u) e1@(AnnE s2 _) = AnnE (s1 <> s2) $ NUnary u e1
{-# inline nUnary #-}

nBinary :: Ann SrcSpan NBinaryOp -> NExprLoc -> NExprLoc -> NExprLoc
nBinary (Ann s1 b) e1@(AnnE s2 _) e2@(AnnE s3 _) =
  AnnE (s1 <> s2 <> s3) $ NBinary b e1 e2

nSelectLoc
  :: Maybe NExprLoc -> NExprLoc -> Ann SrcSpan (NAttrPath NExprLoc) -> NExprLoc
nSelectLoc Nothing e1@(AnnE s2 _) (Ann s1 ats) = AnnE (s2 <> s1) $ NSelect Nothing e1 ats
nSelectLoc (Just e2@(AnnE s3 _)) e1@(AnnE s2 _) (Ann s1 ats) = AnnE (s3 <> s2 <> s1) $ NSelect (pure e2) e1 ats

nHasAttr :: NExprLoc -> Ann SrcSpan (NAttrPath NExprLoc) -> NExprLoc
nHasAttr e1@(AnnE s1 _) (Ann s2 ats) = AnnE (s1 <> s2) $ NHasAttr e1 ats

nApp :: NExprLoc -> NExprLoc -> NExprLoc
nApp e1@(AnnE s1 _) e2@(AnnE s2 _) = AnnE (s1 <> s2) $ NBinary NApp e1 e2

nAbs :: Ann SrcSpan (Params NExprLoc) -> NExprLoc -> NExprLoc
nAbs (Ann s1 ps) e1@(AnnE s2 _) = AnnE (s1 <> s2) $ NAbs ps e1

nStr :: Ann SrcSpan (NString NExprLoc) -> NExprLoc
nStr (Ann s1 s) = AnnE s1 $ NStr s

deltaInfo :: SourcePos -> (Text, Int, Int)
deltaInfo (SourcePos fp l c) = (toText fp, unPos l, unPos c)

nNull :: NExprLoc
nNull = AnnE nullSpan $ NConstant NNull
{-# inline nNull #-}

nullSpan :: SrcSpan
nullSpan = SrcSpan nullPos nullPos
{-# inline nullSpan #-}

-- | Pattern systems for matching on NExprLocF constructions.

--  2021-07-15: NOTE: Make versions of these for NExprLoc, since source code actually uses just fixed versions of these shorthands.
pattern NConstant_ :: SrcSpan -> NAtom -> NExprLocF r
pattern NConstant_ ann x = AnnFP ann (NConstant x)

pattern NStr_ :: SrcSpan -> NString r -> NExprLocF r
pattern NStr_ ann x = AnnFP ann (NStr x)

pattern NSym_ :: SrcSpan -> VarName -> NExprLocF r
pattern NSym_ ann x = AnnFP ann (NSym x)

pattern NList_ :: SrcSpan -> [r] -> NExprLocF r
pattern NList_ ann x = AnnFP ann (NList x)

pattern NSet_ :: SrcSpan -> Recursivity -> [Binding r] -> NExprLocF r
pattern NSet_ ann recur x = AnnFP ann (NSet recur x)

pattern NLiteralPath_ :: SrcSpan -> FilePath -> NExprLocF r
pattern NLiteralPath_ ann x = AnnFP ann (NLiteralPath x)

pattern NEnvPath_ :: SrcSpan -> FilePath -> NExprLocF r
pattern NEnvPath_ ann x = AnnFP ann (NEnvPath x)

pattern NUnary_ :: SrcSpan -> NUnaryOp -> r -> NExprLocF r
pattern NUnary_ ann op x = AnnFP ann (NUnary op x)

pattern NBinary_ :: SrcSpan -> NBinaryOp -> r -> r -> NExprLocF r
pattern NBinary_ ann op x y = AnnFP ann (NBinary op x y)

pattern NSelect_ :: SrcSpan ->  Maybe r -> r -> NAttrPath r -> NExprLocF r
pattern NSelect_ ann v x p = AnnFP ann (NSelect v x p)

pattern NHasAttr_ :: SrcSpan -> r -> NAttrPath r -> NExprLocF r
pattern NHasAttr_ ann x p = AnnFP ann (NHasAttr x p)

pattern NAbs_ :: SrcSpan -> Params r-> r -> NExprLocF r
pattern NAbs_ ann x b = AnnFP ann (NAbs x b)

pattern NLet_ :: SrcSpan -> [Binding r] -> r -> NExprLocF r
pattern NLet_ ann x b = AnnFP ann (NLet x b)

pattern NIf_ :: SrcSpan -> r -> r -> r -> NExprLocF r
pattern NIf_ ann c t e = AnnFP ann (NIf c t e)

pattern NWith_ :: SrcSpan -> r -> r -> NExprLocF r
pattern NWith_ ann x y = AnnFP ann (NWith x y)

pattern NAssert_ :: SrcSpan -> r -> r -> NExprLocF r
pattern NAssert_ ann x y = AnnFP ann (NAssert x y)

pattern NSynHole_ :: SrcSpan -> VarName -> NExprLocF r
pattern NSynHole_ ann x = AnnFP ann (NSynHole x)
{-# complete NConstant_, NStr_, NSym_, NList_, NSet_, NLiteralPath_, NEnvPath_, NUnary_, NBinary_, NSelect_, NHasAttr_, NAbs_, NLet_, NIf_, NWith_, NAssert_, NSynHole_ #-}
