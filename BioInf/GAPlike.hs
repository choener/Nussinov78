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
import Data.Char (toUpper, ord)
import Data.Primitive
import Data.Vector.Fusion.Stream as S
import Data.Vector.Fusion.Stream.Monadic as SM
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import Prelude as P
import "PrimitiveArray" Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU

import ADP.Fusion.GAPlike
import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Zero.Unboxed as PA

import Debug.Trace
import Control.Arrow (second)



-- The signature

type Signature m a r =
  ( ()   -> a
  , Char -> a    -> a
  , a    -> Char -> a
  , Char -> a    -> Char -> a
  , a    -> a    -> a
  , SM.Stream m a -> m r
  )

-- the grammar

gNussinov (empty,left,right,pair,split,h) s b e =
  ( s, (  empty <<< e         |||
          left  <<< b % s     |||
          right <<<     s % b |||
          pair  <<< b % s % b |||
          split <<<  s' % s'  ... h)
  ) where s' = transToN s
{-# INLINE gNussinov #-}

-- pairmax algebra

aPairmax :: (Monad m) => Signature m Int Int
aPairmax = (empty,left,right,pair,split,h) where
  empty   _   = 0
  left    b s = s
  right s b   = s
  pair  l s r = if basepair l r then 1+s else -999999
  {-# INLINE [0] pair #-}
  split  l r  = l+r
  h = SM.foldl1' max
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
  h = return . id
{-# INLINE aPretty #-}

type CombSignature m e b =
  ( () -> (e, m (SM.Stream m b))
  , Char -> (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b))
  , (e, m (SM.Stream m b)) -> Char -> (e, m (SM.Stream m b))
  , Char -> (e, m (SM.Stream m b)) -> Char -> (e, m (SM.Stream m b))
  , (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b))
  , SM.Stream m (e, m (SM.Stream m b)) -> m (SM.Stream m b)
  )

instance Show (Id [String]) where
  show xs = show $ unId xs

(<**)
  :: (Monad m, Eq b, Eq e, Show e, Show (m [b]))
  => Signature m e e
  -> Signature m b (SM.Stream m b)
  -> CombSignature m e b
(<**) f s = (empty,left,right,pair,split,h) where
  (emptyF,leftF,rightF,pairF,splitF,hF) = f
  (emptyS,leftS,rightS,pairS,splitS,hS) = s

  empty e         = (emptyF e   , return $ SM.singleton (emptyS e))
  left b (x,ys)   = (leftF b x  , ys >>= return . SM.map (\y -> leftS b y  ))
  right  (x,ys) b = (rightF x b , ys >>= return . SM.map (\y -> rightS  y b))
  pair l (x,ys) r = (pairF l x r, ys >>= return . SM.map (\y -> pairS l y r))
  split (x,ys) (s,ts) = (splitF x s, ys >>= \ys' -> ts >>= \ts' -> return $ SM.concatMap (\y -> SM.map (\t -> splitS y t) ts') ys')
  h xs = do
    hfs <- hF $ SM.map fst xs
    let phfs = SM.concatMapM snd . SM.filter ((hfs==) . fst) $ xs
    -- trace (">>>" P.++ show (hfs, SM.toList phfs)) $ hS phfs
    hS phfs


-- * Boilerplate and driver, will be moved to library

nussinov78 inp = (arr ! (Z:.0:.n),bt) where
  (_,Z:._:.n) = bounds arr
  len  = P.length inp
  vinp = VU.fromList . P.map toUpper $ inp
  arr  = runST (nussinov78Fill $ vinp)
  bt   = backtrack vinp arr
{-# NOINLINE nussinov78 #-}

-- type TBL s = Tbl E (PA.MArr0 s DIM2 Int)

nussinov78Fill :: forall s . VU.Vector Char -> ST s (Arr0 DIM2 Int)
nussinov78Fill inp = do
  let n = VU.length inp
  t' <- fromAssocsM (Z:.0:.0) (Z:.n:.n) 0 []
  let t = mtblE t'
  let b = Chr inp
  let e = Empty
  fillTable $ gNussinov aPairmax t b e
  freeze t'
{-# NOINLINE nussinov78Fill #-}

fillTable :: PrimMonad m => (MTbl E (MArr0 (PrimState m) DIM2 Int), ((Int,Int) -> m Int)) -> m ()
fillTable (MTbl tbl, f) = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (i,j)
    v `seq` writeM tbl (Z:.i:.j) v
{-# INLINE fillTable #-}

-- * backtracking

backtrack (inp :: VU.Vector Char) (tbl :: PA.Arr0 DIM2 Int) = unId . SM.toList . unId $ g (0,n) where
  n = VU.length inp
  c = Chr inp
  e = Empty
  t = bttblE tbl (g :: BTfun Id String)
  (_,g) = gNussinov (aPairmax <** aPretty) t c e
{-# INLINE backtrack #-}

