{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftTree where

import GHC.NT
import Newtype hiding (main)

data Tree a = T a [Tree a] deriving Show

treeNT :: NT a b -> NT (Tree a) (Tree b)
treeNT = deriveThisNT

main = do
    let n = T (1 :: Int) [T (2 :: Int) []]
    let a = coerce (sym (treeNT ageNT)) n
    print n
    print a

