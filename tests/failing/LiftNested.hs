{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftNested where

import GHC.NT
import Newtype hiding (main)

data Bal a = End a | Node (Bal (a,a)) deriving Show

balNT :: NT a b -> NT (Bal a) (Bal b)
balNT = deriveThisNT


main = do
    let n = Node (Node (End ((1,2),(3,4))))
    let a = coerce (sym (balNT ageNT)) n
    print n
    print a

