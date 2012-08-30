
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
                      mapM_ doGAPlike xs

{-
doNussinov78 inp = do
  putStrLn inp
  let rs = nussinov78 inp
  mapM_ (\(e,bt) -> putStr bt >> printf " %5d\n" e) $ take 10 rs
-}

doGAPlike inp = do
  printf "%s %d\n" inp (G.nussinov78 inp)
