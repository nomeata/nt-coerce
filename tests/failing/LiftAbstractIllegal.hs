{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftAbstract where

import GHC.NT
import Newtype hiding (main)
import Abstract

data WrappedAbstract a = WrappedAbstract (Abs1 a) deriving Show

wrappedAbstactNT :: NT a b -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNT = deriveThisNT

main = do
    let n = WrappedAbstract abs1
    let a = coerce (sym (wrappedAbstactNT ageNT)) n
    print n
    print a

