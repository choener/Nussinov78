{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Strict, scalar nussinov78 algorithm.

module BioInf.Nussinov78 where

import Control.Arrow (first,second,(***))
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.State.Lazy
import "PrimitiveArray" Data.Array.Repa.Index
import qualified Data.Vector.Fusion.Stream as P
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import Biobase.Primary
import Biobase.Secondary.Vienna

import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.Zero

import ADP.Fusion
import ADP.Fusion.Monadic
import ADP.Fusion.Monadic.Internal



-- | Simple RNA folding with basepair maximization.

nussinov78 inp = arr `seq` bt where
  (_,Z:._:.n) = bounds arr
  arr = runST (nussinov78Fill . mkPrimary $ inp)
  bt  = nussinov78BT (mkPrimary inp) arr
{-# NOINLINE nussinov78 #-}

-- | The actual Nussinov78 folding algorithm.

nussinov78Fill :: Primary -> ST s (Arr0 DIM2 Int)
nussinov78Fill inp = do
  let base = base' inp
      {-# INLINE base #-}
  let n = let (_,Z:.l) = bounds inp in l+1
  s <- fromAssocsM (Z:.0:.0) (Z:.n:.n) 0 []

  fillTable s (
                nil   <<< empty               |||
                left  <<< base -~~ s          |||
                right <<<          s ~~- base |||
                pair  <<< base -~~ s ~~- base |||
                split <<<       s +~+ s       ... h
              )
  freeze s
{-# INLINE nussinov78Fill #-}

-- | Fill the single table with values in an orderly fashion. The order in
-- which we fill depends on the algorithm.

fillTable :: PrimMonad m => MArr0 (PrimState m) DIM2 Int -> (DIM2 -> m Int) -> m ()
fillTable tbl f = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (Z:.i:.j)
    writeM tbl (Z:.i:.j) v
    return ()
{-# INLINE fillTable #-}

-- | Request the single character enclosed by (i,i+1), with i+1==j

base' :: Primary -> DIM2 -> (Scalar Nuc)
base' inp (Z:.i:.j) = Scalar $ inp ! (Z:.i)
{-# INLINE base' #-}

-- | True, if the subword at ij is empty.

empty :: DIM2 -> Scalar Bool
empty (Z:.i:.j) = Scalar $ i==j

-- | The base case of our recursion.

nil :: Bool -> Int
nil b = if b then 0 else -999999

-- | A single nucleotide to the left. Note that "x" is monadic. In 'nussinov'
-- we are in the ST monad, here we just know that we are in a monad.

left :: Nuc -> Int -> Int
left l x = x
{-# INLINE left #-}

-- | A single nucleotide to the right.

right :: Int -> Nuc -> Int
right x r = x
{-# INLINE right #-}

-- | Pair function

pair :: Nuc -> Int -> Nuc -> Int
pair l x r
  | basepair l r = x+1
  | otherwise    = -999999
{-# INLINE pair #-}

-- | Combine the partition of x next-to y.

split :: Int -> Int -> Int
split = (+)
{-# INLINE split #-}

-- | Determine if two characters form a legal basepair.

basepair l r
  | mkViennaPair (l,r) /= vpNS = True
basepair _   _   = False
{-# INLINE basepair #-}

-- | the grammar makes sure that we at least have "nil #<< empty" in the stream
h = S.foldl1' max
{-# INLINE h #-}



-- * backtrace secondary structures

type Backtrace = (Int,String)

nussinov78BT :: Primary -> Arr0 DIM2 Int -> [Backtrace]
nussinov78BT inp s = P.toList $ grammar (Z:.0:.n) where
  base = base' inp
  n = let (_,(Z:._:.l)) = bounds s in l
  s' :: DIM2 -> Scalar (DIM2,Int)
  s' ij = Scalar $ (ij,s!ij)

  grammar :: DIM2 -> P.Stream Backtrace
  grammar = (
      nilBT   <<< empty                |||
      leftBT  <<< base -~~ s'          |||
      rightBT <<<          s' ~~- base |||
      pairBT  <<< base -~~ s' ~~- base |||
      splitBT <<<      s' +~+ s'       ..@ hBT)

  nilBT :: Bool -> (Int, P.Stream Backtrace)
  nilBT b      = if b then (0, P.singleton (0,"")) else (0, P.empty)

  leftBT :: Nuc -> (DIM2,Int) -> (Int, P.Stream Backtrace)
  leftBT _ (ij,x)   = (x, P.map (second ("."++)) $ grammar ij)

  rightBT :: (DIM2,Int) -> Nuc -> (Int, P.Stream Backtrace)
  rightBT (ij,x) _  = (x, P.map (second (++".")) $ grammar ij)

  pairBT :: Nuc -> (DIM2,Int) -> Nuc -> (Int, P.Stream Backtrace)
  pairBT l (ij,x) r = if basepair l r then (x+1, P.map (second (\a -> "("++a++")")) $ grammar ij) else (0, P.empty)

  splitBT :: (DIM2,Int) -> (DIM2,Int) -> (Int, P.Stream Backtrace)
  splitBT (ij,x) (kl,y)  = (x+y, P.concatMap (\(s1,bts1) -> P.map (\(s2,bts2) -> (s1+s2,bts1++bts2)) $ grammar kl) $ grammar ij)

  hBT ij = P.concatMap (\(score,bts) -> P.map (first (const score)) bts) . P.filter (\(score,bts) -> score == s!ij)

