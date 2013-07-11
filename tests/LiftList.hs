{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftList where

import GHC.NT
import Newtype hiding (main)

listNT :: NT a b -> NT [a] [b]
listNT = deriveThisNT

main = do
    let n = [1 :: Int]
    let a = coerce (sym (listNT ageNT)) n
    print n
    print a

