{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module Abstract (Abs1, Abs2, abs2NT, abs1, abs2) where

import GHC.NT

data Abs1 a = Abs1 a deriving Show

data Abs2 a = Abs2 a deriving Show

abs2NT :: NT a b -> NT (Abs2 a) (Abs2 b)
abs2NT = deriveThisNT

abs1 :: Abs1 Int
abs1 = Abs1 1

abs2 :: Abs2 Int
abs2 = Abs2 1
