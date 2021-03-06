
-- | Simple wrapper for Nussinov78. We take at most 10 backtracking results --
-- unlimited backtracking would produce an exponential amount of backtracking
-- results. The ambiguity is part of the original algorithm!

module Main where

import Text.Printf
import System.Environment

-- import BioInf.Nussinov78
import qualified BioInf.GAPlike as G



main = do
  as <- getArgs
  print as
  case as of
  {-
    [] -> do xs <- fmap lines getContents
             mapM_ doNussinov78 xs -}
    ["gaplike"] -> do xs <- fmap lines getContents
                      mapM_ (doGAPlike 0) xs
    ["gaplike",k] -> do xs <- fmap lines getContents
                        mapM_ (doGAPlike (read k)) xs

{-
doNussinov78 inp = do
  putStrLn inp
  let rs = nussinov78 inp
  mapM_ (\(e,bt) -> putStr bt >> printf " %5d\n" e) $ take 10 rs
-}

doGAPlike :: Int -> String -> IO ()
doGAPlike k inp = do
  let (n,bt) = G.nussinov78 inp
  n `seq` printf "%s %d\n" inp n
  mapM_ putStrLn $ take k bt
