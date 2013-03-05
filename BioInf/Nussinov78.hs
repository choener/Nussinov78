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

module BioInf.Nussinov78 where

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
import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU

--import ADP.Fusion.GAPlike hiding (E)
--import qualified ADP.Fusion.GAPlike as GAP
import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Zero as Z
import ADP.Fusion
import ADP.Fusion.Apply
import ADP.Fusion.Empty
import ADP.Fusion.Table
import ADP.Fusion.Chr
import Data.Array.Repa.Index.Subword

import Debug.Trace
import Control.Arrow (second)
import System.IO.Unsafe



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

--gNussinov :: Signature m a r -> MTable a -> Chr Char -> Empty -> (MTable a, Subword -> m r)
gNussinov (empty,left,right,pair,split,h) s b e =
  ( s, (
          empty <<< e         |||
          left  <<< b % s     |||
          right <<<     s % b |||
          pair  <<< b % s % b |||
          split <<<  s  % s   ... h
      )
  ) -- where s' = transToN s
{-# INLINE gNussinov #-}

-- pairmax algebra

aPairmax :: (Monad m) => Signature m Int Int
aPairmax = (empty,left,right,pair,split,h) where
  empty   _   = 0
  left    b s = s
  right s b   = s
  pair  l s r = if basepair l r then 1+s else -999999
  split  l r  = l+r
  {-# INLINE split #-}
  h = SM.foldl1' max
  {-# INLINE h #-}
{-# INLINE aPairmax #-}

basepair :: Char -> Char -> Bool
basepair l r = f l r where
  f 'C' 'G' = True
  f 'G' 'C' = True
  f 'A' 'U' = True
  f 'U' 'A' = True
  f 'G' 'U' = True
  f 'U' 'G' = True
  f _   _   = False
{-# INLINE basepair #-}

{-
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
-}

-- * Boilerplate and driver, will be moved to library


nussinov78 inp = (arr ! (Z:.subword 0 n),bt) where
  (_,Z:.Subword (_:.n)) = bounds arr
  len  = P.length inp
  vinp = VU.fromList . P.map toUpper $ inp
  arr  = unsafePerformIO (nussinov78Fill $ vinp)
  bt   = [] :: [String] -- backtrack vinp arr
{-# NOINLINE nussinov78 #-}

-- type TBL s = Tbl E (PA.MArr0 s DIM2 Int)

--nussinov78Fill :: forall s . VU.Vector Char -> ST s (Z.U (Z:.Subword) Int)
nussinov78Fill :: VU.Vector Char -> IO (Z.U (Z:.Subword) Int)
nussinov78Fill inp = do
  let n = VU.length inp
  !t' <- fromAssocsM (Z:.subword 0 0) (Z:.subword 0 n) 0 []
  let t = MTable True t' -- mtblE t'
      {-# INLINE t #-}
  let b = Chr inp
      {-# INLINE b #-}
  let e = Empty
      {-# INLINE e #-}
  fillTable $ gNussinov aPairmax t b e
  freeze t'
{-# NOINLINE nussinov78Fill #-}

fillTable :: PrimMonad m => (MTable (Z.MU m (Z:.Subword) Int), (Subword -> m Int)) -> m ()
fillTable (MTable _ tbl, f) = do
  let (_,Z:.Subword (0:.n)) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- i `seq` j `seq` (f $ subword i j)
    v `seq` writeM tbl (Z:.subword i j) v
{-# INLINE fillTable #-}

{-

-- * backtracking

backtrack (inp :: VU.Vector Char) (tbl :: Z.U DIM2 Int) = unId . SM.toList . unId $ g (0,n) where
  n = VU.length inp
  c = Chr inp
  e = Empty
  t = bttblE tbl (g :: BTfun Id String)
  (_,g) = gNussinov (aPairmax <** aPretty) t c e
{-# INLINE backtrack #-}

-}

