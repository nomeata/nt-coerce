{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

import GHC.NT

newtype Age = Age Int deriving Show

ageNT :: NT Age Int
ageNT = createNT

newtype MyList a = MyList [a] deriving Show

myListNT :: NT (MyList a) [a]
myListNT = createNT


main = do
    let n = 1 :: Int
    let a = coerce (sym ageNT) 1
    let l1 = [a]
    let l2 = coerce (listNT ageNT) l1
    let l3 = coerce (sym myListNT) l2
    print a
    print l2
    print l3

