{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftMultiple where

import GHC.NT
import Newtype hiding (main)

tupleNT :: NT a a' -> NT ((a,b),a) ((a',b),a')
tupleNT = deriveThisNT

main = do
    let n = ((1,True),2)
    let a = coerce (sym (tupleNT ageNT)) n
    print n
    print a

