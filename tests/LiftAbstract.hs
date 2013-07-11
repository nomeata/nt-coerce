{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftAbstract where

import GHC.NT
import Newtype hiding (main)
import Abstract

data WrappedAbstract a = WrappedAbstract (Abs2 a) deriving Show

wrappedAbstactNTRaw :: NT a b -> NT (Abs2 a) (Abs2 b) -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNTRaw = deriveThisNT

wrappedAbstactNT :: NT a b -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNT nt = wrappedAbstactNTRaw nt (abs2NT nt)


main = do
    let n = WrappedAbstract abs2
    let a = coerce (sym (wrappedAbstactNT ageNT)) n
    print n
    print a

