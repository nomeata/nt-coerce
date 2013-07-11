{-# OPTIONS_GHC -fplugin GHC.NT.Plugin #-}

import GHC.NT
import Abstract

listNT :: NT a b -> NT [a] [b]
listNT = deriveThisNT

tupleNT :: NT a b -> NT (a,c) (b,c)
tupleNT = deriveThisNT

nestedNT :: NT a a' -> NT ((a,b),c) ((a',b),c)
nestedNT = deriveThisNT

data Bal a = Leaf a | Node (Bal (a,a))

balNT :: NT a b -> NT (Bal a) (Bal b)
balNT = deriveThisNT

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

data Tree a = T a [Tree a] deriving Show
newtype Tree' a = Tree' (Tree a) deriving Show

treeNT :: NT a b -> NT (Tree a) (Tree b)
treeNT = deriveThisNT

tree'NT :: NT (Tree' a) (Tree a)
tree'NT = deriveThisNT

tree'NT' :: NT a b -> NT (Tree' a) (Tree' b)
tree'NT' = deriveThisNT

data F a b c = F a b c deriving Show

fNT :: NT a a' -> NT (F a b c) (F a' b c)
fNT = deriveThisNT


badNT :: NT a b -> NT (Abs1 a) (Abs1 b)
badNT = deriveThisNT -- rejected 

data WrappedBad a = WrappedBad (Abs1 a) deriving Show
wrappedBadNT :: NT a b -> NT (WrappedBad a) (WrappedBad b)
wrappedBadNT = deriveThisNT -- rejected

data WrappedAbstract a = WrappedAbstract (Abs2 a) deriving Show
wrappedAbstactBadNT :: NT a b -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactBadNT = deriveThisNT -- rejected

wrappedAbstactNTRaw :: NT a b -> NT (Abs2 a) (Abs2 b) -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNTRaw = deriveThisNT -- accepted

wrappedAbstactNT :: NT a b -> NT (WrappedAbstract a) (WrappedAbstract b)
wrappedAbstactNT nt = wrappedAbstactNTRaw nt (abs2NT nt)

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
    tree'NT `seq` tree'NT' `seq` tupleNT `seq` return ()
    -- badNT `seq` return ()
    -- wrappedBadNT `seq` return ()
    -- wrappedAbstactBadNT `seq` return ()
    wrappedAbstactNT `seq` return ()
    let wa = WrappedAbstract abs2
    print wa
    print $ coerce (sym (wrappedAbstactNT ageNT)) wa
    let t1 = T 1 []
    print $ coerce (trans (sym tree'NT) (sym (tree'NT' ageNT))) t1
    print $ coerce (trans (treeNT (sym ageNT)) (sym tree'NT)) t1
    nestedNT `seq` return ()
    -- balNT `seq` return ()

