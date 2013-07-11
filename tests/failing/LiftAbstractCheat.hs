{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module LiftAbstractCheat where

import GHC.NT
import Newtype hiding (main)
import Abstract

data WrappedAbstract a = WrappedAbstract (Abs1 a) deriving Show

wrappedAbstactNTRaw :: NT a b -> NT (Abs1 a) (Abs1 b) -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNTRaw = deriveThisNT

wrappedAbstactNT :: NT a b -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNT nt = wrappedAbstactNTRaw nt (error "You caught me cheating!")


main = do
    let n = WrappedAbstract abs1
    let a = coerce (sym (wrappedAbstactNT ageNT)) n
    print n
    print a

