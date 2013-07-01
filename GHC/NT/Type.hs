{-# LANGUAGE EmptyDataDecls #-}
{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

module GHC.NT.Type where

data NT a b -- = NT (a,b)
