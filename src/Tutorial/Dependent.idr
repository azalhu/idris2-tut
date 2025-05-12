module Tutorial.Dependent

%default total

bogusMapList : (a -> b) -> List a -> List b
bogusMapList _ _ = Nil

bogusZipList : (a -> b -> c) -> List a -> List b -> List c
bogusZipList _ _ _ = Nil

data Vect : (len : Nat) -> (a : Type) -> Type where
  Nil : Vect Z a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

Eq a => Eq (Vect n a) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

ex1 : Vect 0 Integer
ex1 = Nil

failing "Mismatch between: S ?n and 0."
  ex2 : Vect 0 Integer
  ex2 = [12]

ex3 : Vect 1 Integer
ex3 = [12]

data Indexed : Nat -> Type where
  I0 : Indexed 0
  I3 : Indexed 3
  I4 : String -> Indexed 4

fromIndexed : Indexed n -> a -> Vect n a
fromIndexed (I0)   va = []
fromIndexed (I3)   va = [va, va, va]
fromIndexed (I4 _) va = [va, va, va, va]

map3_1 : (a -> b) -> Vect 3 a -> Vect 1 b
map3_1 f [_,y,_] = [f y]

map5_0 : (a -> b) -> Vect 5 a -> Vect 0 b
map5_0 f _ = []

map5_10 : (a -> b) -> Vect 5 a -> Vect 10 b
map5_10 f [u,v,w,x,y] = [f u, f u, f v, f v, f w, f w, f x, f x, f y, f y]

mapVect' : (a -> b) -> Vect n a -> Vect n b
mapVect' f [] = []
mapVect' f (x :: xs) = (f x :: mapVect' f xs)

mapVect : {0 a,b : _} -> {0 n : Nat} -> (a -> b) -> Vect n a -> Vect n b
mapVect f [] = []
mapVect f (x :: xs) = (f x :: mapVect f xs)

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith f [] (y :: ys) impossible
zipWith f (x :: xs) [] impossible

failing "Mismatch between: S ?n and n."
  fill : a -> Vect n a
  fill va = [va,va]

--fill' : {0 a : Type} -> {0 n : Nat} -> a -> Vect n a
fill' : {0 a : Type} -> {n : Nat} -> a -> Vect n a
fill' {n=Z} _ = []
fill' {n=S k} va = va :: fill' {n=k} va

replicate : (n : Nat) -> a -> Vect n a
replicate 0 _ = []
replicate (S k) va = va :: replicate k va

head : Vect (S n) a -> a
head (x :: xs) = x
head [] impossible

tail : Vect (S n) a -> Vect n a
tail (x :: xs) = xs
tail [] impossible

zipWith3 : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
zipWith3 f [] [] [] = []
zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

foldSemi : Semigroup a => List a -> Maybe a
foldSemi Nil = Nothing
foldSemi (x :: xs) = Just . maybe x (x <+>) $ foldSemi xs

foldSemi' : Semigroup a => Vect (S n) a -> a
foldSemi' (x :: Nil) = x
foldSemi' (x :: xs@(_ :: _)) = x <+> foldSemi' xs

--foldSemi : Semigroup a => List a -> List a -> List a
--foldSemi [] ys = ys
--foldSemi xs [] = xs
--foldSemi (x :: xs) (y :: ys) = x <+> y :: foldSemi xs ys
--
--foldSemi' : Semigroup a => Vect (S n) a -> Vect (S n) a -> Vect (S n) a
--foldSemi' (x :: Nil) (y :: Nil) = x <+> y :: []
--foldSemi' (x :: x' :: xs) (y :: y' :: ys) = x <+> y :: foldSemi' (x' :: xs) (y' :: ys)
--foldSemi' [] [] impossible
--foldSemi' (x :: xs) [] impossible
--foldSemi' [] (y :: ys) impossible

iterate : (n : Nat) -> (a -> a) -> a -> Vect n a
iterate Z _ _ = []
iterate (S k) f va = va :: iterate k f (f va)

generate : (n : Nat) -> (fun : s -> (s,a)) -> s -> Vect n a
generate Z _ _ = []
generate (S k) f s = let (s',va) = f s in va :: generate k f s'

fromList : (as : List a) -> Vect (length as) a
fromList [] = []
fromList (x :: xs) = x :: fromList xs

maybeSize : Maybe a -> Nat
maybeSize = maybe 0 (const 1)

fromMaybe : (m : Maybe a) -> Vect (maybeSize m) a
fromMaybe Nothing = []
fromMaybe (Just x) = [x]

indexList : (pos : Nat) -> List a -> Maybe a
indexList _ [] = Nothing
indexList 0 (x :: _) = Just x
indexList (S k) (_ :: xs) = indexList k xs

data Fin : (n : Nat) -> Type where
  FZ : {0 n : Nat} -> Fin (S n)
  FS : (k : Fin n) -> Fin (S n)

fin0_5 : Fin 5
fin0_5 = FZ

fin0_7 : Fin 7
fin0_7 = FZ

fin1_3 : Fin 3
fin1_3 = FS FZ

fin4_5 : Fin 5
fin4_5 = FS $ FS $ FS $ FS FZ

index : Fin n -> Vect n a -> a
index FZ (x :: _) = x
index (FS k) (_ :: xs) = index k xs
index _ Nil impossible

update : Fin n -> (a -> a) -> Vect n a -> Vect n a
update FZ f (x :: xs) = f x :: xs
update (FS k) f (x :: xs) = x :: update k f xs

insert : Fin (S n) -> a -> Vect n a -> Vect (S n) a
insert FZ va xs = va :: xs
insert (FS k) va (x :: xs) = x :: insert k va xs

delete : Fin (S n) -> Vect (S n) a -> Vect n a
delete FZ (_ :: xs) = xs
delete (FS k) (x :: xs@(_ :: _)) = x :: delete k xs

safeIndexList : (as : List a) -> Fin (length as) -> a
safeIndexList (x :: _) FZ = x
safeIndexList (_ :: xs) (FS k) = safeIndexList xs k

finToNat : Fin n -> Nat
finToNat FZ = Z
finToNat (FS k) = S $ finToNat k

natToFin : (n : Nat) -> Fin (S n)
natToFin Z = FZ
natToFin (S k) = FS (natToFin k)

take : (fin : Fin (S n)) -> Vect n a -> Vect (finToNat fin) a
take FZ _ = Nil
take (FS k) (x :: xs) = x :: take k xs

minus : (n : Nat) -> Fin (S n) -> Nat
minus j FZ = j
minus (S j) (FS k) = minus j k

drop : (fin : Fin (S n)) -> Vect n a -> Vect (minus n fin) a
drop FZ xs = xs
drop (FS k) (_ :: xs) = drop k xs

splitAt : (fin : Fin (S n)) ->
          (as : Vect n a) ->
          (Vect (finToNat fin) a, Vect (minus n fin) a)
splitAt k xs = (take k xs, drop k xs)

(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

drop' : (m : Nat) -> Vect (m + n) a -> Vect n a
drop' Z xs = xs
drop' (S k) (_ :: xs) = drop' k xs

add : Nat -> Nat -> Nat
add Z n = n
add (S k) n = S $ add k n

failing "Can't solve constraint between: plus n 1 and S n."
  reverse : Vect n a -> Vect n a
  reverse [] = []
  reverse (x :: xs) = reverse xs ++ [x]

ex4 : Vect 3 Integer
ex4 = zipWith (*) (replicate 3 10) (replicate 3 11)

ex5 : Vect 3 Integer
ex5 = zipWith (*) (replicate _ 10) (replicate _ 11)

replicate' : {n : _} -> a -> Vect n a
replicate' = replicate n

ex6 : Vect ? Bool
ex6 = replicate' {n = 2} True

replicate'' : {n : _} -> a -> Vect n a
replicate'' {n = Z}   _ = Nil
replicate'' {n = S _} v = v :: replicate'' v

flattenList : List (List a) -> List a
flattenList [] = []
flattenList (xs :: xss) = xs ++ flattenList xss

flattenVect : Vect m (Vect n a) -> Vect (m * n) a
flattenVect [] = []
flattenVect (xs :: xss) = xs ++ flattenVect xss

take' : (m : Nat) -> Vect (m + n) a -> Vect m a
take' Z _ = Nil
take' (S k) (x :: xs) = x :: take' k xs

splitAt' : (m : Nat) -> Vect (m + n) a -> (Vect m a, Vect n a)
splitAt' k xs = (take' k xs, drop' k xs)

transpose : {n : _} -> Vect m (Vect n a) -> Vect n (Vect m a)
transpose {n = Z}   _  = []
transpose {n = S _} xs =
  let heads = mapVect head xs
      tails = mapVect tail xs in
      heads :: transpose tails

transpose' : {n : _} -> Vect m (Vect n a) -> Vect n (Vect m a)
transpose' [] = replicate' []
transpose' (xs :: xss) = zipWith (::) xs (transpose' xss)

t_test : Bool
t_test = transpose [[1],[2]] == [[1,2]]

transpose_test : Bool
transpose_test = transpose [[1,2,3],[4,5,6]] == [[1,4],[2,5],[3,6]]

