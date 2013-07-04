{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module GHC.NT (NT, coerce, refl, sym, trans, deriveThisNT) where

import GHC.NT.Type

coerce :: NT a b -> a -> b
coerce = error "GHC.NT.coerce"

refl   :: NT a a
refl = error "GHC.NT.refl"

sym    :: NT a b -> NT b a
sym = error "GHC.NT.sym"

trans  :: NT a b -> NT b c -> NT a c
trans = error "GHC.NT.trans"

deriveThisNT :: a
deriveThisNT = error "left over deriveThis. Did GHC.NT.Plugin run?"
{-# NOINLINE deriveThisNT #-}

