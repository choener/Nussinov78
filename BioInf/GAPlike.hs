{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BioInf.GAPlike where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.ST
import Data.Vector.Fusion.Stream as S
import Data.Vector.Fusion.Stream.Monadic as SM
import Data.Vector.Fusion.Stream.Size
import "PrimitiveArray" Data.Array.Repa.Index
import Data.Char (toUpper, ord)
import Prelude as P
import qualified Data.Vector.Unboxed as VU
import Data.Primitive

import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Unboxed.Zero as PA
import ADP.Fusion.GAPlike

import Debug.Trace



-- the grammar

gNussinov (empty,left,right,pair,split,h) s b e =
  ( s, (  empty <<< e         |||
          left  <<< b % s     |||
          right <<< s % b     |||
          pair  <<< b % s % b |||
          split <<< s % s     ..@ h)
  )
{-# INLINE gNussinov #-}

-- The signature

type Signature m a r =
  ( ()   -> a
  , Char -> a    -> a
  , a    -> Char -> a
  , Char -> a    -> Char -> a
  , a    -> a    -> a
  , (Int,Int) -> SM.Stream m a -> m r
  )

type CombSignature m x a r =
  ( ()   -> a
  , Char -> a    -> a
  , a    -> Char -> a
  , Char -> a    -> Char -> a
  , a    -> a    -> a
  , Arr0 DIM2 x -> (Int,Int) -> SM.Stream m a -> m r
  )

-- pairmax algebra

aPairmax :: (Monad m) => Signature m Int Int
aPairmax = (empty,left,right,pair,split,h) where
  empty   _   = 0
  left    b s = s
  right s b   = s
  pair  l s r = if basepair l r then 1+s else s
  {-# INLINE [0] pair #-}
  split  l r  = l+r
  h _ = SM.foldl1' max
  basepair l r = f l r where
    f 'C' 'G' = True
    f 'G' 'C' = True
    f 'A' 'U' = True
    f 'U' 'A' = True
    f 'G' 'U' = True
    f 'U' 'G' = True
    f _   _   = False
  {-# INLINE basepair #-}
{-# INLINE aPairmax #-}

aPretty :: (Monad m) => Signature m String (SM.Stream m String)
aPretty = (empty,left,right,pair,split,h) where
  empty _     = ""
  left  b s   = "." P.++ s
  right   s b = s P.++ "."
  pair  l s r = "(" P.++ s P.++ ")"
  split l   r = l P.++ r
  h _ = return . id
{-# INLINE aPretty #-}

aProduct
  :: (Monad m, VU.Unbox as, Prim as, Eq as)
  => Signature m as at
  -> Signature m bs bt
  -> Arr0 DIM2 as
  -> CombSignature m as (as,bs) (SM.Stream m (as,bs))
aProduct a b tbl = (empty,left,right,pair,split,h) where
  (emptya,lefta,righta,paira,splita,ha) = a
  (emptyb,leftb,rightb,pairb,splitb,hb) = b
  empty ()       = (emptya (), emptyb ())
  left b (sa,sb) = (lefta b sa, leftb b sb)
  right (sa,sb) b = (righta sa b, rightb sb b)
  pair b (sa,sb) c = (paira b sa c, pairb b sb c)
  split (la,lb) (ra,rb) = (splita la ra, splitb lb rb)
  h tbl (i,j) xs = return . SM.filter ((tbl!(Z:.i:.j) ==) . fst) $ xs


-- * Boilerplate and driver, will be moved to library

nussinov78 inp = arr ! (Z:.0:.n) where
  (_,Z:._:.n) = bounds arr
  len = P.length inp
  arr = runST (nussinov78Fill . VU.fromList . P.map toUpper $ inp)
{-# NOINLINE nussinov78 #-}

-- type TBL s = Tbl E (PA.MArr0 s DIM2 Int)

nussinov78Fill :: forall s . VU.Vector Char -> ST s (Arr0 DIM2 Int)
nussinov78Fill inp = do
  let n = VU.length inp
  t' <- fromAssocsM (Z:.0:.0) (Z:.n:.n) 0 []
  let t = MTbl t' -- :: TBL s
  let b = Chr inp
      {-# INLINE b #-}
  let e = Empty
      {-# INLINE e #-}
  fillTable $ gNussinov aPairmax t b e
  freeze t'
{-# INLINE nussinov78Fill #-}

fillTable :: PrimMonad m => (MTbl E (MArr0 (PrimState m) DIM2 Int), ((Int,Int) -> m Int)) -> m ()
fillTable (MTbl tbl, f) = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (i,j)
    v `seq` writeM tbl (Z:.i:.j) v
{-# INLINE fillTable #-}

-- * backtracking

nussinov78BT :: VU.Vector Char -> Arr0 DIM2 Int -> [String]
nussinov78BT inp tbl = undefined -- gNussinov (aProduct aPairmax aPretty tbl) tbl (Chr inp) (0,VU.length inp)
