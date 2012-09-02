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

import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Unboxed.VectorZero as PA
import ADP.Fusion.GAPlike2

import Debug.Trace



-- the grammar

gNussinov (left,right,pair,split,h) s b =
  ( s, (  left  <<< b % s     |||
          right <<< s % b     |||
          pair  <<< b % s % b |||
          split <<< s % s     ... h)
  )
{-# INLINE gNussinov #-}

-- The signature

type Signature m a r =
  ( Char -> a    -> a
  , a    -> Char -> a
  , Char -> a    -> Char -> a
  , a    -> a    -> a
  , SM.Stream m a -> m r
  )

-- pairmax algebra

aPairmax :: (Monad m) => Signature m Int Int
aPairmax = (left,right,pair,split,h) where
  left    b s = s
  right s b   = s
  pair  l s r = if basepair l r then 1+s else s
  split  l r  = l+r
  h = SM.foldl' max 0
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

aPretty :: (Monad m) => Signature m String [String]
aPretty = (left,right,pair,split,h) where
  left  b s   = "." P.++ s
  right   s b = s P.++ "."
  pair  l s r = "(" P.++ s P.++ ")"
  split l   r = l P.++ r
  h = SM.toList
{-# INLINE aPretty #-}

aProduct :: (Monad m) => Signature m as at -> Signature m bs bt -> Signature m (as,bs) bt
aProduct a b tbl = (left,right,pair,split,h) where
  (lefta,righta,paira,splita,ha) = a
  (leftb,rightb,pairb,splitb,hb) = b
  left b (sa,sb) = (lefta b sa, leftb b sb)
  right (sa,sb) b = (righta sa b, rightb sb b)
  pair b (sa,sb) c = (paira b sa c, pairb b sb c)
  split (la,lb) (ra,rb) = (paira la ra, pairb lb rb)
  h = undefined
  {-
  h xs = [ (xa,xb)
         | (xa,xb) <- xs
         , xa == tbl
         ] -}

-- * Boilerplate and driver, will be moved to library

nussinov78 inp = arr ! (Z:.0:.n) where
  (_,Z:._:.n) = bounds arr
  len = P.length inp
  arr = runST (nussinov78Fill . VU.fromList . P.map toUpper $ inp)
{-# NOINLINE nussinov78 #-}

type TBL s = Tbl E (PA.MArr0 s DIM2 Int)

nussinov78Fill :: forall s . VU.Vector Char -> ST s (Arr0 DIM2 Int)
nussinov78Fill inp = do
  let n = VU.length inp
  t' <- fromAssocsM (Z:.0:.0) (Z:.n:.n) 0 []
  let t = Tbl t' :: TBL s
  let b = Chr inp
      {-# INLINE b #-}
  fillTable $ gNussinov aPairmax t b
  freeze t'
{-# INLINE nussinov78Fill #-}

fillTable :: PrimMonad m => (Tbl E (MArr0 (PrimState m) DIM2 Int), ((Int,Int) -> m Int)) -> m ()
fillTable (Tbl tbl, f) = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (i,j)
    v `seq` writeM tbl (Z:.i:.j) v
{-# INLINE fillTable #-}

-- * backtracking

-- nussinov78BT :: VU.Vector Char -> Arr0 DIM2 Int -> [String]
-- nussinov78BT inp tbl = gNussinov ((<**) aPairmax aPretty tbl) tbl (Chr inp) (0,VU.length inp)
