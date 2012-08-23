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

import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Unboxed.Zero as PA
import ADP.Fusion.GAPlike

import Debug.Trace
import ADP.Fusion.Monadic.Internal (Apply(..))



-- the grammar

gNussinov (nil,left,right,pair,split,h) empty b s =
  ( s, (  nil   <<< empty     |||
          left  <<< b % s     |||
          right <<< s % b     |||
          pair  <<< b % s % b |||
          split <<< s % s     ... h)
  )
{-# INLINE gNussinov #-}

type BLA m =
  ( () -> Int
  , Char -> Int  -> Int
  , Int  -> Char -> Int
  , Char -> Int  -> Char -> Int
  , Int  -> Int  -> Int
  , SM.Stream m Int -> m Int
  )

-- pairmax algebra

aPairmax :: (Monad m) => BLA m
aPairmax = (nil,left,right,pair,split,h) where
  nil ()      = 0
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



nussinov78 inp = arr ! (Z:.0:.n) where
  (_,Z:._:.n) = bounds arr
  len = P.length inp
  arr = runST (nussinov78Fill . PA.fromList (Z:.0) (Z:.len-1) . P.map toUpper $ inp)
{-# NOINLINE nussinov78 #-}


-- let's fill a table

nussinov78Fill :: Arr0 DIM1 Char -> ST s (Arr0 DIM2 Int)
nussinov78Fill inp = do
  let n = let (_,Z:.l) = bounds inp in l+1
  s <- fromAssocsM (Z:.0:.0) (Z:.n:.n) 0 []
  let b = PAsingle inp
      {-# INLINE b #-}
  let e = Empty
  fillTable $ gNussinov aPairmax e b s
  freeze s
{-# INLINE nussinov78Fill #-}


fillTable :: PrimMonad m => (MArr0 (PrimState m) DIM2 Int, (DIM2 -> m Int)) -> m ()
fillTable (tbl, f) = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (Z:.i:.j)
    writeM tbl (Z:.i:.j) v
    return ()
{-# INLINE fillTable #-}


data Empty = Empty

type instance TopIdx Empty = Int

type instance TopArg Empty = ()

instance Build Empty where
  type Bld Empty = Z:.Empty
  build a = Z:.a
  {-# INLINE build #-}

instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.Empty) where
  type SC (x:.Empty) = ()
  mkStreamInner (x:._) (Z:.i:.j) = SM.flatten mk step Unknown $ mkStreamInner x (Z:.i:.j) where
    mk :: MkType m x Empty
    mk (zi:.k,za) = return $ (zi:.k:.k,za)
    step :: StepType m x Empty
    step (zi:.k:.l,za)
      | l==j      = return $ S.Yield (zi:.k:.l,za:.()) (zi:.k:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamInner #-}
  mkStream = mkStreamInner
  {-# INLINE mkStream #-}



