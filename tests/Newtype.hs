{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module Newtype where

import GHC.NT

newtype Age = Age Int deriving Show

ageNT :: NT Age Int
ageNT = deriveThisNT

main = do
    let n = 1 :: Int
    let a = coerce (sym ageNT) 1
    print n
    print a

