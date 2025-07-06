module Tutorial.PrimLib

import Data.DPair
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total

-- Like `Dec` but with erased proofs. Constructors `Yes0`
-- and `No0` will be converted to constants `0` and `1` by
-- the compiler!
data Dec0 : (prop : Type) -> Type where
  Yes0 : (0 prf : prop) -> Dec0 prop
  No0  : (0 contra : prop -> Void) -> Dec0 prop

-- For interfaces with more than one parameter (`a` and `p`
-- in this example) sometimes one parameter can be determined
-- by knowing the other. For instance, if we know what `p` is,
-- we will most certainly also know what `a` is. We therefore
-- specify that proof search on `Decidable` should only be
-- base on `p` by listing `p` after a vertical bar: `| p`.
-- This is like specifying the search parameter(s) of
-- a data type with '[search p]' as was shown in the chapter
-- about predicates.
-- Specifying a single search parameter as shown here can
-- drastically help with type inference.
interface Decidable (0 a : Type) (0 p : a -> Type) | p where
  decide : (v : a) -> Dec0 (p v)

-- We often have to pass `p` explicitly in order to help Idris with
-- type inference. In such cases, it is more convenient to use
-- `decideOn pred` instead of `decide {p = pred}`.
decideOn : (0 p : a -> Type) -> Decidable a p => (v : a) -> Dec0 (p v)
decideOn _ = decide

-- Some primitive predicates can only be reasonably implemented
-- using boolean functions. This utility helps with decidability
-- on such proofs.
test0 : (b : Bool) -> Dec0 (b === True)
test0 True  = Yes0 Refl
test0 False = No0 absurd

data IsYes0 : (d : Dec0 prop) -> Type where
  ItIsYes0 : {0 prf : _} -> IsYes0 (Yes0 prf)

0 fromYes0 : (d : Dec0 prop) -> (0 prf : IsYes0 d) => prop
fromYes0 (Yes0 x) = x
fromYes0 (No0 contra) impossible

0 safeDecideOn :  (0 p : a -> Type)
               -> Decidable a p
               => (v : a)
               -> (0 prf : IsYes0 (decideOn p v))
               => p v
safeDecideOn p v = fromYes0 $ decideOn p v

-- only use this if you are sure that `decideOn p v`
-- will return a `Yes0`!
0 unsafeDecideOn : (0 p : a -> Type) -> Decidable a p => (v : a) -> p v
unsafeDecideOn p v = case decideOn p v of
  Yes0 prf => prf
  No0  _   =>
    assert_total $ idris_crash "Unexpected refinement failure in `unsafeDecideOn`"


--  1 --

{x : a} -> DecEq a => Decidable a (Equal x) where
  decide v = case decEq x v of
    Yes prf    => Yes0 prf
    No  contra => No0 contra

--  2 --

data Neg : (p : a -> Type) -> a -> Type where
  IsNot : {0 p : a -> Type} -> (contra : p v -> Void) -> Neg p v

Decidable a p => Decidable a (Neg p) where
  decide v = case decideOn p v of
    Yes0 prf    => No0 $ \(IsNot contra) => contra prf
    No0  contra => Yes0 $ IsNot contra

--  3 --

data (&&) : (p,q : a -> Type) -> a -> Type where
  Both : {0 p,q : a -> Type} -> (prf1 : p v) -> (prf2 : q v) -> (&&) p q v

Decidable a p => Decidable a q => Decidable a (p && q) where
  decide v = case decideOn p v of
    Yes0 prf1   => case decideOn q v of
      Yes0 prf2   => Yes0 $ Both prf1 prf2
      No0  contra => No0 $ \(Both _ prf2) => contra prf2
    No0  contra => No0 $ \(Both prf1 _) => contra prf1

--  4 --

data (||) : (p,q : a -> Type) -> a -> Type where
  L : {0 p : a -> Type} -> (prf : p v) -> (||) p q v
  R : {0 q : a -> Type} -> (prf : q v) -> (||) p q v

Decidable a p => Decidable a q => Decidable a (p || q) where
  decide v = case decideOn p v of
    Yes0 prf    => Yes0 $ L prf
    No0 contra1 => case decideOn q v of
      Yes0 prf     => Yes0 $ R prf
      No0  contra2 => No0 $ \case L prf => contra1 prf
                                  R prf => contra2 prf

--  5 --

negOr : Neg (p || q) v -> (Neg p && Neg q) v
negOr (IsNot contra) = Both (IsNot $ contra . L) (IsNot $ contra . R)

andNeg : (Neg p && Neg q) v -> Neg (p || q) v
andNeg (Both (IsNot c1) (IsNot c2)) =
  IsNot $ \case L p1 => c1 p1
                R p2 => c2 p2

orNeg : (Neg p || Neg q) v -> Neg (p && q) v
orNeg (L (IsNot contra)) = IsNot $ \(Both p1 _) => contra p1
orNeg (R (IsNot contra)) = IsNot $ \(Both _ p2) => contra p2

0 negAnd :  Decidable a p
         => Decidable a q
         => Neg (p && q) v
         -> (Neg p || Neg q) v
negAnd (IsNot contra) = case decideOn p v of
  Yes0 p1 => case decideOn q v of
    Yes0 p2 => void $ contra $ Both p1 p2
    No0  c  => R $ IsNot c
  No0  c  => L $ IsNot c


--  Intermezzo


-- Proof that m <= n
data (<=) : (m,n : Nat) -> Type where
  ZLTE : Z <= n
  SLTE : m <= n -> S m <= S n

(>=) : (m,n : Nat) -> Type
m >= n = n <= m

(<) : (m,n : Nat) -> Type
m < n = S m <= n

(>) : (m,n : Nat) -> Type
m > n = n < m

LessThan : (m,n : Nat) -> Type
LessThan m = (< m)

To : (m,n : Nat) -> Type
To m = (<= m)

GreaterThan : (m,n : Nat) -> Type
GreaterThan m = (> m)

From : (m,n : Nat) -> Type
From m = (>= m)

FromTo : (lower,upper : Nat) -> Nat -> Type
FromTo l u = From l && To u

Between : (lower,upper : Nat) -> Nat -> Type
Between l u = GreaterThan l && LessThan u

Uninhabited (S m <= Z) where
  uninhabited ZLTE impossible
  uninhabited (SLTE _) impossible


--  6 --

0 fromLTE : (n1,n2 : Nat) -> (n1 <= n2) === True -> n1 <= n2
fromLTE Z      _      _   = ZLTE
fromLTE (S n1) (S n2) prf = SLTE $ fromLTE n1 n2 prf
fromLTE (S _)  Z      prf = absurd prf

0 toLTE : (n1,n2 : Nat) -> n1 <= n2 -> (n1 <= n2) === True
toLTE Z      Z      ZLTE       = Refl
toLTE Z      (S _)  ZLTE       = Refl
toLTE (S n1) (S n2) (SLTE prf) = toLTE n1 n2 prf
toLTE (S _)  Z      prf        = absurd prf

{n : _} -> Decidable Nat (<= n) where
  decide m = case test0 (m <= n) of
    Yes0 prf    => Yes0 $ fromLTE m n prf
    No0  contra => No0 $ contra . toLTE m n

{m : _} -> Decidable Nat (m <=) where
  decide n = case test0 (m <= n) of
    Yes0 prf    => Yes0 $ fromLTE m n prf
    No0  contra => No0 $ contra . toLTE m n

--  7 --

0 refl : {n : Nat} -> n <= n
refl {n = Z}   = ZLTE
refl {n = S _} = SLTE refl

0 trans : {n : Nat} -> l <= m -> m <= n -> l <= n
trans ZLTE     _        = ZLTE
trans (SLTE x) (SLTE y) = SLTE $ trans x y

0 (>>) : {l,m,n : Nat} -> l <= m -> m <= n -> l <= n
(>>) = trans

--  8 --

0 toIsSucc : n > Z -> IsSucc n
toIsSucc (SLTE _) = ItIsSucc
toIsSucc ZLTE impossible

0 fromIsSucc : IsSucc n -> n > Z
fromIsSucc ItIsSucc = SLTE ZLTE

--  9 --

safeDiv : (x,y : Bits64) -> (0 prf : cast y > Z) => Bits64
safeDiv x y = x `div` y

safeMod :  (x,y : Bits64)
        -> (0 prf : cast y > Z)
        => Subset Bits64 (\v => cast v < cast y)
safeMod x y = Element (x `mod` y) (unsafeDecideOn (<= cast y) _)

-- 10 --

digit : (v : Bits64) -> (0 prf : cast v < 16) => Char
digit 0  = '0'
digit 1  = '1'
digit 2  = '2'
digit 3  = '3'
digit 4  = '4'
digit 5  = '5'
digit 6  = '6'
digit 7  = '7'
digit 8  = '8'
digit 9  = '9'
digit 10 = 'a'
digit 11 = 'b'
digit 12 = 'c'
digit 13 = 'd'
digit 14 = 'e'
digit 15 = 'f'
digit x = assert_total $ idris_crash "IMPOSSIBLE: Invalid digit (\{show x})"

record Base where
  constructor MkBase
  value : Bits64
  0 prf : FromTo 2 16 (cast value)

base : Bits64 -> Maybe Base
base v = case decideOn (FromTo 2 16) (cast v) of
  Yes0 prf => Just $ MkBase v prf
  No0  _   => Nothing

namespace Base
  public export
  fromInteger : (v : Integer) -> (0 prf : IsJust (base $ cast v)) => Base
  fromInteger v = fromJust $ base (cast v)

logN : Bits64 -> Bits64 -> Bits64
logN x b = go (cast x) 0
  where go : Nat -> Bits64 -> Bits64
        go Z acc = acc
        go k acc =
          let d = k `div` cast b
           in go (assert_smaller k d) (acc + 1)

digits' : Bits64 -> Base -> String
digits' x (MkBase b $ Both p1 p2) = pack $ go (cast $ logN x b) Nil x
  where go : Nat -> List Char -> Bits64 -> List Char
        go Z     cs _ = cs
        go (S k) cs v =
          let Element d p = (v `safeMod` b) {prf = %search >> p1}
              v2          = (v `safeDiv` b) {prf = %search >> p1}
           in go k (digit d {prf = p >> p2} :: cs) v2

digits : Bits64 -> Base -> String
digits 0 _ = "0"
digits x (MkBase b $ Both p1 p2) = go Nil x
  where go : List Char -> Bits64 -> String
        go cs 0 = pack cs
        go cs v =
          let Element d p = (v `safeMod` b) {prf = %search >> p1}
              v2          = (v `safeDiv` b) {prf = %search >> p1}
           in go (digit d {prf = p >> p2} :: cs) (assert_smaller v v2)

testDigits' : String
testDigits' = case base 16 of
  Just b  => digits' 333 b
  Nothing => ""

testDigits : Maybe String
testDigits = base 16 >>= Just . digits 333

-- 11 --

data CharOrd : (p : Nat -> Type) -> Char -> Type where
  IsCharOrd : {0 p : Nat -> Type} -> (prf : p (cast c)) -> CharOrd p c

Decidable Nat p => Decidable Char (CharOrd p) where
  decide v = case decideOn p (cast v) of
    Yes0 prf   => Yes0 $ IsCharOrd prf
    No0 contra => No0 $ \(IsCharOrd prf) => contra prf

IsAscii : Char -> Type
IsAscii = CharOrd (< 127)

IsLatin : Char -> Type
IsLatin = CharOrd (< 256)

IsUpper : Char -> Type
IsUpper = CharOrd (FromTo (cast 'A') (cast 'Z'))

IsLower : Char -> Type
IsLower = CharOrd (FromTo (cast 'a') (cast 'z'))

IsAlpha : Char -> Type
IsAlpha = IsUpper || IsLower

IsDigit : Char -> Type
IsDigit = CharOrd (FromTo (cast '0') (cast '9'))

IsAlphaNum : Char -> Type
IsAlphaNum = IsAlpha || IsDigit

IsControl : Char -> Type
IsControl = CharOrd (FromTo 0 31 || FromTo 127 159)

IsPlainAscii : Char -> Type
IsPlainAscii = IsAscii && Neg IsControl

IsPlainLatin : Char -> Type
IsPlainLatin = IsLatin && Neg IsControl

-- 12 --

0 plainToAscii : IsPlainAscii c -> IsAscii c
plainToAscii (Both prf1 _) = prf1

0 digitToAlphaNum : IsDigit c -> IsAlphaNum c
digitToAlphaNum = R

0 alphaToAlphaNum : IsAlpha c -> IsAlphaNum c
alphaToAlphaNum = L

0 lowerToAlpha : IsLower c -> IsAlpha c
lowerToAlpha = R

0 upperToAlpha : IsUpper c -> IsAlpha c
upperToAlpha = L

0 lowerToAlphaNum : IsLower c -> IsAlphaNum c
lowerToAlphaNum = L . R

0 upperToAlphaNum : IsUpper c -> IsAlphaNum c
upperToAlphaNum = L . L

0 asciiToLatin : IsAscii c -> IsLatin c
asciiToLatin (IsCharOrd x) = IsCharOrd (x >> safeDecideOn _ _)

0 plainAsciiToPlainLatin : IsPlainAscii c -> IsPlainLatin c
plainAsciiToPlainLatin (Both x y) = Both (asciiToLatin x) y

-- 13 --

data Head : (p : a -> Type) -> List a -> Type where
  AtHead : {0 p : a -> Type} -> (0 prf : p v) -> Head p (v :: vs)

Uninhabited (Head p Nil) where
  uninhabited AtHead impossible

Decidable a p => Decidable (List a) (Head p) where
  decide Nil       = No0 $ \prf => absurd prf
  decide (x :: _) = case decideOn p x of
    Yes0 prf => Yes0 $ AtHead prf
    No0 contra => No0 $ \(AtHead prf) => contra prf

-- 14 --

data Length : (p : Nat -> Type) -> List a -> Type where
  HasLength :  {0 p : Nat -> Type}
            -> (0 prf : p (List.length vs))
            -> Length p vs

Decidable Nat p => Decidable (List a) (Length p) where
  decide vs = case decideOn p (length vs) of
    Yes0 prf   => Yes0 $ HasLength prf
    No0 contra => No0 $ \(HasLength prf) => contra prf

-- 15 --

data All : (p : a -> Type) -> (as : List a) -> Type where
  Nil  :  All p Nil
  (::) :  {0 p : a -> Type}
       -> (0 h : p v)
       -> (0 t : All p vs)
       -> All p (v :: vs)

data AllSnoc : (p : a -> Type) -> (as : SnocList a) -> Type where
  Lin  :  AllSnoc p Lin
  (:<) :  {0 p : a -> Type}
       -> (0 i : AllSnoc p vs)
       -> (0 l : p v)
       -> AllSnoc p (vs :< v)

0 head : All p (x :: xs) -> p x
head (h :: _) = h

0 (<>>) : AllSnoc p sx -> All p xs -> All p (sx <>> xs)
Lin    <>> y = y
i :< l <>> y = i <>> l :: y

0 suffix : (sx : SnocList a) -> All p (sx <>> xs) -> All p xs
suffix Lin       x = x
suffix (sx :< y) x = let (_ :: t) = suffix {xs = y :: xs} sx x in t

0 notInner :  {0 p : a -> Type}
           -> (sx : SnocList a)
           -> (0 contra : (prf : p x) -> Void)
           -> (0 prfs : All p (sx <>> x :: xs))
           -> Void
notInner sx contra prfs = contra $ head $ suffix sx prfs

allTR : {0 p : a -> Type} -> Decidable a p => (as : List a) -> Dec0 (All p as)
allTR as = go Lin as
  where go : (0 sp : AllSnoc p sx) -> (xs : List a) -> Dec0 (All p (sx <>> xs))
        go sp Nil       = Yes0 $ sp <>> Nil
        go sp (x :: xs) = case decideOn p x of
          Yes0 prf   => go (sp :< prf) xs
          No0 contra => No0 $ \prf => notInner sx contra prf

Decidable a p => Decidable (List a) (All p) where decide = allTR

-- 16 --

0 IsIdentChar : Char -> Type
IsIdentChar = IsAlphaNum || Equal '_'

0 IdentChars : List Char -> Type
IdentChars = Length (<= 100) && Head IsAlpha && All IsIdentChar

record Identifier where
  constructor MkIdentifier
  value : String
  0 prf : IdentChars (unpack value)

identifier : String -> Maybe Identifier
identifier s = case decideOn IdentChars (unpack s) of
  Yes0 prf => Just $ MkIdentifier s prf
  No0 _    => Nothing

namespace Identifier
  public export
  fromString :  (s : String)
             -> (0 _ : IsYes0 (decideOn IdentChars (unpack s)))
             => Identifier
  fromString s = MkIdentifier s (fromYes0 $ decide (unpack s))

testIdent : Identifier
testIdent = "fooBar_123"

