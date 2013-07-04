{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

import GHC.NT

listNT :: NT a b -> NT [a] [b]
listNT = deriveThisNT

newtype Age = Age Int deriving Show

ageNT :: NT Age Int
ageNT = deriveThisNT

newtype MyList a = MyList [a] deriving Show

myListNT :: NT (MyList a) [a]
myListNT = deriveThisNT

foo :: NT a b -> NT (MyList a) (MyList b)
foo = deriveThisNT

newtype R a = R [R a] deriving Show

rNT :: NT (R a) [R a]
rNT = deriveThisNT

-- Would not work (but is removed anyways before it is seen by GHC.NT.Plugin)
bar :: NT (MyList Age) [Int]
bar = deriveThisNT

data F a b c = F a b c deriving Show

fNT :: NT a a' -> NT (F a b c) (F a' b c)
fNT = deriveThisNT

main = do
    let n = 1 :: Int
    let a = coerce (sym ageNT) 1
    let l1 = [a]
    let l2 = coerce (listNT ageNT) l1
    let l3 = coerce (sym myListNT) l2
    print a
    print l2
    print l3
    print $ coerce (foo (sym ageNT)) l3
    --print $ coerce bar (MyList [a])
    print $ coerce (sym rNT) []
    print $ coerce (fNT (sym ageNT)) (F 1 2 3)

