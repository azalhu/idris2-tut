module Tutorial.TutFolds

import Data.List1
import Data.Maybe
import Data.Stream
import Data.Vect
import Debug.Trace
import Tutorial.TutFunctor

%default total

replicateList : Nat -> a -> List a
replicateList Z     _ = Nil
replicateList (S k) x = x :: replicateList k x

-- Can also be made point-free (go : List a -> Nat -> a -> List a)
replicateListTR : Nat -> a -> List a
replicateListTR n v = go Nil n
  where go : List a -> Nat -> List a
        go xs Z     = xs
        go xs (S k) = go (v :: xs) k

replicateVect : (n : Nat) -> a -> Vect n a
replicateVect Z     _ = Nil
replicateVect (S k) x = x :: replicateVect k x

len : List a -> Nat
len Nil       = Z
len (_ :: xs) = S $ len xs

lenOnto : Nat -> List a -> Nat
lenOnto k Nil       = k
lenOnto k (_ :: xs) = lenOnto (S k) xs

lenTR : List a -> Nat
lenTR = lenOnto Z

lenTR' : List a -> Nat
lenTR' = lenOnto' Z
  where lenOnto' : Nat -> List a -> Nat
        lenOnto' k Nil       = k
        lenOnto' k (_ :: xs) = lenOnto' (S k) xs

lenTR'' : List a -> Nat
lenTR'' = let lenOnto'' : Nat -> List a -> Nat
              lenOnto'' k Nil       = k
              lenOnto'' k (_ :: xs) = lenOnto'' (S k) xs
           in lenOnto'' Z

covering
unfold : (gen : s -> Maybe (s,a)) -> s -> List a
unfold gen vs = case gen vs of
  Just (vs',va) => va :: unfold gen vs'
  Nothing       => Nil

fiboHelper : (Nat,Nat) -> ((Nat,Nat),Nat)
fiboHelper (f0,f1) = ((f1, f0 + f1),f0)

covering
fibonacci : List Nat
fibonacci = unfold (Just . fiboHelper) (1,1)

unfoldTot : Nat -> (gen : s -> Maybe (s,a)) -> s -> List a
unfoldTot Z     _   _  = Nil
unfoldTot (S k) gen vs = case gen vs of
  Just (vs',va) => va :: unfoldTot k gen vs'
  Nothing       => Nil

fibonacciN : Nat -> List Nat
fibonacciN n = unfoldTot n (Just . fiboHelper) (1,1)

main : IO ()
main = printLn . len $ replicateList 10000 10

main1 : IO ()
main1 = printLn . lenTR $ replicateListTR 10000 10

countTR : (a -> Bool) -> List a -> Nat
countTR p = go Z
  where go : Nat -> List a -> Nat
        go k Nil       = k
        go k (x :: xs) = case p x of
          True  => go (S k) xs
          False => go k xs

mainCount : IO ()
mainCount = printLn $ countTR (`mod` 2 == 0) [1..1000]

countStreamTR : (a -> Bool) -> Nat -> Stream a -> Nat
countStreamTR p = go Z
  where go : Nat -> Nat -> Stream a -> Nat
        go k Z     _         = k
        go k (S j) (x :: xs) = case p x of
          True  => go (S k) j xs
          False => go k j xs

succeed : Stream Nat
succeed = iterate S Z

mainStreamCount : IO ()
mainStreamCount = printLn $ countStreamTR (`mod` 2 == 0) 100000 succeed

even : Nat -> Bool

odd : Nat -> Bool

even Z     = True
even (S k) = odd k

odd Z     = False
odd (S k) = even k

mutual
  even' : Nat -> Bool
  even' Z     = True
  even' (S k) = odd' k

  odd' : Nat -> Bool
  odd' Z     = False
  odd' (S k) = even' k

main2 : IO ()
main2 =  printLn (even 100000)
      >> printLn (odd 100000)

anyList' : (a -> Bool) -> List a -> Bool
anyList' _ Nil       = False
anyList' p (x :: xs) = case p x of
  True  => True
  False => anyList' p xs

allList' : (a -> Bool) -> List a -> Bool
allList' _ Nil       = True
allList' p (x :: xs) = case p x of
  True  => allList' p xs
  False => False

findList' : (a -> Bool) -> List a -> Maybe a
findList' _ Nil       = Nothing
findList' p (x :: xs) = case p x of
  True  => Just x
  False => findList' p xs

collectList' : (a -> Maybe b) -> List a -> Maybe b
collectList' _ Nil       = Nothing
collectList' f (x :: xs) = case f x of
  Just res => Just res
  Nothing  => collectList' f xs


anyList : (a -> Bool) -> List a -> Bool
anyList p = go False
  where go : Bool -> List a -> Bool
        go False (x :: xs) = go (p x) xs
        go res   _         = res

allList : (a -> Bool) -> List a -> Bool
allList p = go True
  where go : Bool -> List a -> Bool
        go True (x :: xs) = go (p x) xs
        go res  _         = res

findList : (a -> Bool) -> List a -> Maybe a
findList p = go Nothing
  where go : Maybe a -> List a -> Maybe a
        go Nothing (x :: xs) = go (if p x then Just x else Nothing) xs
        go res     _         = res

collectList : (a -> Maybe b) -> List a -> Maybe b
collectList f = go Nothing
  where go : Maybe b -> List a -> Maybe b
        go Nothing (x :: xs) = go (f x) xs
        go res     _         = res

lookupList : Eq a => a -> List (a,b) -> Maybe b
lookupList va = collectList go
  where go : (a,b) -> Maybe b
        go (k,v) = toMaybe (k == va) v

mapTR : (a -> b) -> List a -> List b
mapTR f = go Lin
  where go : SnocList b -> List a -> List b
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (sx :< f x) xs

filterTR : (a -> Bool) -> List a -> List a
filterTR p = go Lin
  where go : SnocList a -> List a -> List a
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (if p x then sx :< x else sx) xs

mapMaybeTR : (a -> Maybe b) -> List a -> List b
mapMaybeTR f = go Lin
  where go : SnocList b -> List a -> List b
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (case f x of Just x' => sx :< x'; _ => sx) xs

catMaybesTR : List (Maybe a) -> List a
catMaybesTR = TutFolds.mapMaybeTR id

concatTR' : List a -> List a -> List a
concatTR' xs ys = (Lin <>< xs) <>> ys

concatTR : List a -> List a -> List a
concatTR = go . (Lin <><)
  where go : SnocList a -> List a -> List a
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (sx :< x) xs

bindTR : List a -> (a -> List b) -> List b
bindTR xs f = go Lin xs
  where go : SnocList b -> List a -> List b
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (sx <>< f x) xs

joinTR : List (List a) -> List a
joinTR xs = go Lin xs
  where go : SnocList a -> List (List a) -> List a
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (sx <>< x) xs

joinTR' : List (List a) -> List a
joinTR' xs = bindTR xs id

covering
replicatePrim : Bits32 -> a -> List a
replicatePrim 0 _ = Nil
replicatePrim x v = v :: replicatePrim (x - 1) v

replicatePrim' : Bits32 -> a -> List a
replicatePrim' 0 _ = Nil
replicatePrim' x v = v :: replicatePrim' (assert_smaller x $ x - 1) v

proofOfVoid : Bits8 -> Void
proofOfVoid n = proofOfVoid (assert_smaller n n)

exFalsoQuodlibet : Void -> a
exFalsoQuodlibet _ impossible

coerce : a -> b
coerce _ = exFalsoQuodlibet $ proofOfVoid 0

pain : IO ()
pain = putStrLn $ coerce 0

record Tree a where
  constructor Node
  value  : a
  forest : List (Tree a)

Forest : Type -> Type
Forest = List . Tree

covering
size : Tree a -> Nat
size (Node _ forest) = S . sum $ map size forest

mutual
  treeSize : Tree a -> Nat
  treeSize (Node _ forest) = S $ forestSize forest

  forestSize : Forest a -> Nat
  forestSize Nil       = Z
  forestSize (x :: xs) = treeSize x + forestSize xs

namespace BadShow
  Show a => Show (Tree a) where
    showPrec p (Node v ts) =
      assert_total $ showCon p "Node" (showArg v ++ showArg ts)

mutual
  treeDepth : Tree a -> Nat
  treeDepth (Node _ ts)  = S $ forestDepth ts

  forestDepth : Forest a -> Nat
  forestDepth Nil       = Z
  forestDepth (t :: ts) = max (treeDepth t) (forestDepth ts)

treeEq : Eq a => Tree a -> Tree a -> Bool
treeEq (Node lv lf) (Node rv rf) = lv == rv && go lf rf
  where go : Forest a -> Forest a -> Bool
        go Nil       Nil       = True
        go (x :: xs) (y :: ys) = treeEq x y && go xs ys
        go _         _         = False

Eq a => Eq (Tree a) where
  (==) = treeEq

treeMap : (a -> b) -> Tree a -> Tree b
treeMap f (Node v ts) = Node (f v) $ go ts
  where go : Forest a -> Forest b
        go Nil       = Nil
        go (x :: xs) = treeMap f x :: go xs

Functor Tree where
  map = treeMap

treeShowPrec : Show a => Prec -> Tree a -> String
treeShowPrec p (Node v ts) = showCon p "Node" $ showArg v ++ go ts
  where go : Forest a -> String
        go Nil       = ""
        go (x :: xs) = " (" ++ treeShowPrec p x ++ ")" ++ go xs

Show a => Show (Tree a) where
  showPrec = treeShowPrec

mutual
  treeToVect : (t : Tree a) -> Vect (treeSize t) a
  treeToVect (Node v forest) = v :: forestToVect forest

  forestToVect : (f : Forest a) -> Vect (forestSize f) a
  forestToVect Nil       = Nil
  forestToVect (x :: xs) = treeToVect x ++ forestToVect xs

leftFold : (acc : state -> el -> state) -> (st : state) -> List el -> state
leftFold _   st Nil       = st
leftFold acc st (x :: xs) = leftFold acc (acc st x) xs

sumLF : Num a => List a -> a
sumLF = leftFold (+) 0

reverseLF : List a -> List a
reverseLF = leftFold (flip (::)) Nil

toSnocListLF : List a -> SnocList a
toSnocListLF = leftFold (:<) Lin

rightFold : (acc : el -> state -> state) -> (st : state) -> List el -> state
rightFold _   st Nil       = st
rightFold acc st (x :: xs) = acc x $ rightFold acc st xs

foldHead : List a -> Maybe a
foldHead = force . rightFold first Nothing
  where first : a -> Lazy (Maybe a) -> Lazy (Maybe a)
        first v _ = Just v

foldHeadTraced : List a -> Maybe a
foldHeadTraced = force . rightFold first Nothing
  where first : a -> Lazy (Maybe a) -> Lazy (Maybe a)
        first v _ = trace "folded" (Just v)

foldHeadTracedStrict : List a -> Maybe a
foldHeadTracedStrict = rightFold first Nothing
  where first : a -> Maybe a -> Maybe a
        first v _ = trace "folded" (Just v)

foldHeadTR : List a -> Maybe a
foldHeadTR Nil      = Nothing
foldHeadTR (x :: _) = Just x

foldMapList : Monoid m => (a -> m) -> List a -> m
foldMapList f = leftFold (\vm,va => vm <+> f va) neutral

concatList : Monoid m => List m -> m
concatList = foldMapList id

Semigroup Integer where
  (<+>) l n = l + n

Monoid Integer where
  neutral = 0

data Crud : (i : Type) -> (a : Type) -> Type where
  Create : (value : a) -> Crud i a
  Update : (id : i) -> (value : a) -> Crud i a
  Read   : (id : i) -> Crud i a
  Delete : (id : i) -> Crud i a

Foldable (Crud i) where
  foldr acc st (Create v)   = acc v st
  foldr acc st (Update _ v) = acc v st
  foldr _   st (Read _)     = st
  foldr _   st (Delete _)   = st

  foldl acc st (Create v)   = acc st v
  foldl acc st (Update _ v) = acc st v
  foldl _   st (Read _)     = st
  foldl _   st (Delete _)   = st

  null (Create _)   = False
  null (Update _ _) = False
  null (Read _)     = True
  null (Delete _)   = True

  foldlM acc st (Create v)   = acc st v
  foldlM acc st (Update _ v) = acc st v
  foldlM _   st (Read _)     = pure st
  foldlM _   st (Delete _)   = pure st

  toList (Create v)   = [v]
  toList (Update _ v) = [v]
  toList (Read _)     = []
  toList (Delete _)   = []

  foldMap f (Create v)   = f v
  foldMap f (Update _ v) = f v
  foldMap _ (Read _)     = neutral
  foldMap _ (Delete _)   = neutral

data Response : (e, i, a : Type) -> Type where
  Created : (id : i) -> (value : a) -> Response e i a
  Updated : (id : i) -> (value : a) -> Response e i a
  Found   : (values : List a) -> Response e i a
  Deleted : (id : i) -> Response e i a
  Error   : (err : e) -> Response e i a

Foldable (Response e i) where
  foldr acc st (Created _ v) = acc v st
  foldr acc st (Updated _ v) = acc v st
  foldr acc st (Found vs)    = foldr acc st vs
  foldr _   st (Deleted _)   = st
  foldr _   st (Error _)     = st

  foldl acc st (Created _ v) = acc st v
  foldl acc st (Updated _ v) = acc st v
  foldl acc st (Found vs)    = foldl acc st vs
  foldl _   st (Deleted _)   = st
  foldl _   st (Error _)     = st

  null (Created _ _) = False
  null (Updated _ _) = False
  null (Found vs)    = null vs
  null (Deleted _)   = True
  null (Error _)     = True

  foldlM acc st (Created _ v) = acc st v
  foldlM acc st (Updated _ v) = acc st v
  foldlM acc st (Found vs)    = foldlM acc st vs
  foldlM _   st (Deleted _)   = pure st
  foldlM _   st (Error _)     = pure st

  toList (Created _ v) = [v]
  toList (Updated _ v) = [v]
  toList (Found vs)    = vs
  toList (Deleted _)   = []
  toList (Error _)     = []

  foldMap f (Created _ v) = f v
  foldMap f (Updated _ v) = f v
  foldMap f (Found vs)    = foldMap f vs
  foldMap _ (Deleted _)   = neutral
  foldMap _ (Error _)     = neutral

Foldable (List01 ne) where
  foldr _   st Nil       = st
  foldr acc st (x :: xs) = acc x $ foldr acc st xs

  foldl _   st Nil       = st
  foldl acc st (x :: xs) = foldl acc (acc st x) xs

  null Nil      = True
  null (_ :: _) = False

  foldlM _   st Nil       = pure st
  foldlM acc st (x :: xs) = acc st x >>= flip (foldlM acc) xs
  --foldlM acc st = foldl (\st',x => st' >>= flip acc x) $ pure st

  toList = go Lin
    where go : SnocList a -> List01 _ a -> List a
          go sx Nil       = sx <>> Nil
          go sx (x :: xs) = go (sx :< x) xs

  foldMap f = go neutral
    where go : m -> List01 _ a -> m
          go acc Nil       = acc
          go acc (x :: xs) = go (acc <+> f x) xs

treeFoldr :  (acc : el -> state -> state)
          -> (st : state)
          -> Tree el
          -> state
treeFoldr acc st (Node v f) = acc v $ go st f
  where go : state -> Forest el -> state
        go st Nil       = st
        go st (x :: xs) = treeFoldr acc (go st xs) x

treeFoldl :  (acc : state -> el -> state)
          -> (st : state)
          -> Tree el
          -> state
treeFoldl acc st (Node v f) = go (acc st v) f
  where go : state -> Forest el -> state
        go st Nil       = st
        go st (x :: xs) = go (treeFoldl acc st x) xs

treeNull : Tree a -> Bool
treeNull = const False

treeFoldlM :  Monad m
           => (acc : state -> el -> m state)
           -> (st : state)
           -> Tree el
           -> m state
treeFoldlM acc st = treeFoldl (\st',x => st' >>= flip acc x) $ pure st

treeToList : Tree a -> List a
treeToList (Node v f) = go [<v] f
  where go : SnocList a -> Forest a -> List a
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (sx <>< treeToList x) xs

treeFoldMap : Monoid m => (g : a -> m) -> Tree a -> m
treeFoldMap g (Node v f) = go (g v) f
  where go : m -> Forest a -> m
        go acc Nil       = acc
        go acc (x :: xs) = go (acc <+> treeFoldMap g x) xs

Foldable Tree where
  foldr   = treeFoldr
  foldl   = treeFoldl
  null    = treeNull
  foldlM  = treeFoldlM
  toList  = treeToList
  foldMap = treeFoldMap

Foldable f => Foldable g => Foldable (Comp f g) where
  foldr acc st (MkComp v) = acc ?a $ ?rhs

Foldable f => Foldable g => Foldable (Product f g) where
  foldr = ?rls

