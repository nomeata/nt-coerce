{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module GHC.NT (NT, coerce, refl, sym, trans, createNT, listNT) where

import GHC.NT.Type

coerce :: NT a b -> a -> b
coerce = error "GHC.NT.coerce"

refl   :: NT a a
refl = error "GHC.NT.refl"

sym    :: NT a b -> NT b a
sym = error "GHC.NT.sym"

trans  :: NT a b -> NT b c -> NT a c
trans = error "GHC.NT.trans"

createNT :: NT a b
createNT = error "GHC.NT.createNT"
{-# NOINLINE createNT #-}

listNT :: NT a b -> NT [a] [b]
listNT = error "GHC.NT.liftNT"

