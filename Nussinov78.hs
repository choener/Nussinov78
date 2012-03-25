
-- | Simple wrapper for Nussinov78. We take at most 10 backtracking results --
-- unlimited backtracking would produce an exponential amount of backtracking
-- results. The ambiguity is part of the original algorithm!

module Main where

import Text.Printf

import BioInf.Nussinov78



main = do
  xs <- fmap lines getContents
  mapM_ doNussinov78 xs

doNussinov78 inp = do
  putStrLn inp
  let rs = nussinov78 inp
  mapM_ (\(e,bt) -> putStr bt >> printf " %5d\n" e) $ take 10 rs
