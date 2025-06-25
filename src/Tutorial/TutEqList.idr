module Tutorial.TutEqList

import Data.Either
import Data.HList
import Data.Vect
import Data.String

import Decidable.Equality

%default total



--  *** Types ***



data ColType = I64 | Str | Boolean | Float

Eq ColType where
  I64     == I64     = True
  Str     == Str     = True
  Boolean == Boolean = True
  Float   == Float   = True
  I64     == _       = False
  Str     == _       = False
  Boolean == _       = False
  Float   == _       = False

Uninhabited (Equal I64 Str) where
  uninhabited Refl impossible

Uninhabited (Equal I64 Boolean) where
  uninhabited Refl impossible

Uninhabited (Equal I64 Float) where
  uninhabited Refl impossible

Uninhabited (Equal Str I64) where
  uninhabited Refl impossible

Uninhabited (Equal Str Boolean) where
  uninhabited Refl impossible

Uninhabited (Equal Str Float) where
  uninhabited Refl impossible

Uninhabited (Equal Boolean I64) where
  uninhabited Refl impossible

Uninhabited (Equal Boolean Str) where
  uninhabited Refl impossible

Uninhabited (Equal Boolean Float) where
  uninhabited Refl impossible

Uninhabited (Equal Float I64) where
  uninhabited Refl impossible

Uninhabited (Equal Float Str) where
  uninhabited Refl impossible

Uninhabited (Equal Float Boolean) where
  uninhabited Refl impossible

DecEq ColType where
  decEq I64 I64         = Yes Refl
  decEq I64 Str         = No absurd
  decEq I64 Boolean     = No absurd
  decEq I64 Float       = No absurd

  decEq Str I64         = No absurd
  decEq Str Str         = Yes Refl
  decEq Str Boolean     = No absurd
  decEq Str Float       = No absurd

  decEq Boolean I64     = No absurd
  decEq Boolean Str     = No absurd
  decEq Boolean Boolean = Yes Refl
  decEq Boolean Float   = No absurd

  decEq Float I64       = No absurd
  decEq Float Str       = No absurd
  decEq Float Boolean   = No absurd
  decEq Float Float     = Yes Refl

data SameColType : (c1,c2 : ColType) -> Type where
  SameCT : SameColType c c

Uninhabited (SameColType I64 Str) where
  uninhabited SameCT impossible

Uninhabited (SameColType I64 Boolean) where
  uninhabited SameCT impossible

Uninhabited (SameColType I64 Float) where
  uninhabited SameCT impossible

Uninhabited (SameColType Str I64) where
  uninhabited SameCT impossible

Uninhabited (SameColType Str Boolean) where
  uninhabited SameCT impossible

Uninhabited (SameColType Str Float) where
  uninhabited SameCT impossible

Uninhabited (SameColType Boolean I64) where
  uninhabited SameCT impossible

Uninhabited (SameColType Boolean Str) where
  uninhabited SameCT impossible

Uninhabited (SameColType Boolean Float) where
  uninhabited SameCT impossible

Uninhabited (SameColType Float I64) where
  uninhabited SameCT impossible

Uninhabited (SameColType Float Str) where
  uninhabited SameCT impossible

Uninhabited (SameColType Float Boolean) where
  uninhabited SameCT impossible

Schema : Type
Schema = List ColType

data SameSchema : (s1,s2 : Schema) -> Type where
  Same : SameSchema s s

Uninhabited (SameSchema Nil (_ :: _)) where
  uninhabited Same impossible

Uninhabited (SameSchema (_ :: _) Nil) where
  uninhabited Same impossible

IdrisType : ColType -> Type
IdrisType I64     = Int64
IdrisType Str     = String
IdrisType Boolean = Bool
IdrisType Float   = Double

Row : Schema -> Type
Row = HList . map IdrisType

record Table where
  constructor MkTable
  schema : Schema
  size   : Nat
  rows   : Vect size (Row schema)

Id : a -> a
Id = id



--  *** Functions ***



sameColType : (c1,c2 : ColType) -> Maybe (SameColType c1 c2)
sameColType I64     I64     = Just SameCT
sameColType Str     Str     = Just SameCT
sameColType Boolean Boolean = Just SameCT
sameColType Float   Float   = Just SameCT
sameColType I64     _       = Nothing
sameColType Str     _       = Nothing
sameColType Boolean _       = Nothing
sameColType Float   _       = Nothing

sameNil : SameSchema Nil Nil
sameNil = Same

sameCons :  SameColType c1 c2
         -> SameSchema s1 s2
         -> SameSchema (c1 :: s1) (c2 :: s2)
sameCons SameCT Same = Same

sameSchema : (s1,s2 : Schema) -> Maybe (SameSchema s1 s2)
sameSchema Nil       Nil       = Just sameNil
sameSchema (x :: xs) Nil       = Nothing
sameSchema Nil       (y :: ys) = Nothing
sameSchema (x :: xs) (y :: ys) =
  [| sameCons (sameColType x y) (sameSchema xs ys) |]

concatTables : Table -> Table -> Maybe Table
concatTables (MkTable s1 _ rs1) (MkTable s2 _ rs2) = case sameSchema s1 s2 of
  Just Same => Just $ MkTable _ _ (rs1 ++ rs2)
  Nothing   => Nothing

concatTables1 : Table -> Table -> Maybe Table
concatTables1 (MkTable s1 m rs1) (MkTable s2 n rs2) = case s1 == s2 of
  True  => ?what_now--Just $ MkTable s1 (m + n) (rs1 ++ rs2)
  False => Nothing

concatTables2 : Table -> Table -> Maybe Table
concatTables2 (MkTable s1 m rs1) (MkTable s2 n rs2) = case sameSchema s1 s2 of
  Just Same => ?almost_there
  Nothing   => Nothing

eqColType : (c1,c2 : ColType) -> Maybe (c1 = c2)
eqColType I64     I64     = Just Refl
eqColType Str     Str     = Just Refl
eqColType Boolean Boolean = Just Refl
eqColType Float   Float   = Just Refl
eqColType I64     _       = Nothing
eqColType Str     _       = Nothing
eqColType Boolean _       = Nothing
eqColType Float   _       = Nothing

eqCons :  {0 c1,c2 : ColType}
       -> {0 s1,s2 : Schema}
       -> c1 = c2
       -> s1 = s2
       -> c1 :: s1 = c2 :: s2
eqCons Refl Refl = Refl

eqSchema : (s1,s2 : Schema) -> Maybe (s1 = s2)
eqSchema Nil       Nil       = Just Refl
eqSchema (x :: xs) Nil       = Nothing
eqSchema Nil       (y :: ys) = Nothing
eqSchema (x :: xs) (y :: ys) = [| eqCons (eqColType x y) (eqSchema xs ys) |]

concatTables3 : Table -> Table -> Maybe Table
concatTables3 (MkTable s1 _ rs1) (MkTable s2 _ rs2) =
  (\Refl => MkTable _ _ (rs1 ++ rs2)) <$> eqSchema s1 s2

onePlusOne : the Nat 1 + 1 = 2
onePlusOne = Refl

onePlusOneWrong : the Nat 1 + 1 = 3

onePlusOneWrongProvably : the Nat 1 + 1 = 3 -> Void
onePlusOneWrongProvably Refl impossible

mapListLength : (f : a -> b) -> (as : List a) -> length as = length (map f as)
mapListLength f Nil       = Refl
mapListLength f (x :: xs) = cong S $ mapListLength f xs

showColType : ColType -> String
showColType I64     = "i64"
showColType Str     = "str"
showColType Boolean = "boolean"
showColType Float   = "float"

readColType : String -> Maybe ColType
readColType "i64"     = Just I64
readColType "str"     = Just Str
readColType "boolean" = Just Boolean
readColType "float"   = Just Float
readColType _         = Nothing

showReadColType : (c : ColType) -> readColType (showColType c) = Just c
showReadColType I64     = Refl
showReadColType Str     = Refl
showReadColType Boolean = Refl
showReadColType Float   = Refl

mapMaybeId : (ma : Maybe a) -> map Prelude.id ma = ma
mapMaybeId Nothing  = Refl
mapMaybeId (Just x) = Refl

mapMaybeId1 : (ma : Maybe a) -> map id_ ma = ma
mapMaybeId1 Nothing  = Refl
mapMaybeId1 (Just x) = ?mapMaybeId1_rhs

mapMaybeId2 : (ma : Maybe a) -> map Id ma = ma
mapMaybeId2 Nothing  = Refl
mapMaybeId2 (Just x) = Refl

notSameLength1 : (List.length as = length bs -> Void) -> as = bs -> Void
notSameLength1 contra prf = contra (cong length prf)

notSameLength : Not (List.length as = length bs) -> Not (as = bs)
notSameLength contra prf = contra (cong length prf)

contraCong : {0 f : _} -> Not (f a = f b) -> Not (a = b)
contraCong contra prf = contra $ cong f prf

decSameColType : (c1,c2 : ColType) -> Dec (SameColType c1 c2)
decSameColType I64 I64         = Yes SameCT
decSameColType I64 Str         = No absurd
decSameColType I64 Boolean     = No absurd
decSameColType I64 Float       = No absurd

decSameColType Str I64         = No absurd
decSameColType Str Str         = Yes SameCT
decSameColType Str Boolean     = No absurd
decSameColType Str Float       = No absurd

decSameColType Boolean I64     = No absurd
decSameColType Boolean Str     = No absurd
decSameColType Boolean Boolean = Yes SameCT
decSameColType Boolean Float   = No absurd

decSameColType Float I64       = No absurd
decSameColType Float Str       = No absurd
decSameColType Float Boolean   = No absurd
decSameColType Float Float     = Yes SameCT

decSameSchema' : (s1,s2 : Schema) -> Dec (SameSchema s1 s2)
decSameSchema' Nil       Nil       = Yes Same
decSameSchema' (x :: xs) Nil       = No ?decss1
decSameSchema' Nil       (y :: ys) = No ?decss2
decSameSchema' (x :: xs) (y :: ys) = case decSameColType x y of
  Yes SameCT => case decSameSchema' xs ys of
    Yes Same  => Yes Same
    No contra => No $ \prf => ?decss3
  No contra  => No $ \prf => ?decss4

consInjective :  SameSchema (c1 :: cs1) (c2 :: cs2)
              -> (SameColType c1 c2, SameSchema cs1 cs2)
consInjective Same = (SameCT, Same)

decSameSchema : (s1,s2 : Schema) -> Dec (SameSchema s1 s2)
decSameSchema Nil       Nil       = Yes Same
decSameSchema (x :: xs) Nil       = No absurd
decSameSchema Nil       (y :: ys) = No absurd
decSameSchema (x :: xs) (y :: ys) = case decSameColType x y of
  Yes SameCT => case decSameSchema xs ys of
    Yes Same  => Yes Same
    No contra => No $ contra . snd . consInjective
  No contra  => No $ contra . fst . consInjective

leftZero :  List (Vect n Nat)
         -> List (Vect (Z + n) Nat)
         -> List (Vect n Nat)
leftZero = (++)

rightZero' :  List (Vect n Nat)
           -> List (Vect (n + Z) Nat)
           -> List (Vect n Nat)
rightZero' l r = ?zr

addZeroRight : (n : Nat) -> n + Z = n
addZeroRight Z     = Refl
addZeroRight (S k) = cong S $ addZeroRight k

replaceNVect : Vect (n + Z) a -> Vect n a
replaceNVect as = replace {p = \k => Vect k a} (addZeroRight n) as

rightZero'' :  List (Vect n Nat)
            -> List (Vect (n + Z) Nat)
            -> List (Vect n Nat)
rightZero'' = map replaceNVect .: flip const

rewriteVect : Vect (n + Z) a -> Vect n a
rewriteVect as = rewrite sym (addZeroRight n) in as

rightZero :  List (Vect n Nat)
          -> List (Vect (n + Z) Nat)
          -> List (Vect n Nat)
rightZero = map rewriteVect .: flip const

revOnto' : Vect m a -> Vect n a -> Vect (m + n) a
revOnto' xs Nil       = ?ron--xs
revOnto' xs (x :: ys) = ?roc--revOnto' (x :: xs) ys

reverseVect' : Vect n a -> Vect n a
reverseVect' = revOnto' Nil

revOnto : Vect m a -> Vect n a -> Vect (m + n) a
revOnto xs Nil       = rewrite (addZeroRight m) in xs
revOnto {n = S len}
        xs (x :: ys) =
  rewrite sym (plusSuccRightSucc m len) in revOnto (x :: xs) ys



--  *** Exercises 1 ***



sctReflexive : SameColType c1 c1
sctReflexive = SameCT

sctSymmetric : SameColType c1 c2 -> SameColType c2 c1
sctSymmetric SameCT = SameCT

sctTransitive : SameColType c1 c2 -> SameColType c2 c3 -> SameColType c1 c3
sctTransitive SameCT SameCT = SameCT

sctCongruent :  {f : ColType -> a}
             -> SameColType c1 c2
             -> f c1 = f c2
sctCongruent SameCT = Refl

eqNat : (m,n : Nat) -> Maybe (m = n)
eqNat Z     Z     = Just Refl
eqNat (S k) Z     = Nothing
eqNat Z     (S j) = Nothing
eqNat (S k) (S j) = (\prf => cong S prf) <$> eqNat k j

appRows : {ts1 : _} -> Row ts1 -> Row ts2 -> Row (ts1 ++ ts2)
appRows {ts1 = Nil}    Nil       ys = ys
appRows {ts1 = h :: t} (x :: xs) ys = x :: appRows xs ys

zipTables : Table -> Table -> Maybe Table
zipTables (MkTable _ m rs1) (MkTable _ n rs2) =
  (\Refl => MkTable _ _ (zipWith appRows rs1 rs2)) <$> eqNat m n



--  *** Exercises 2 ***



mapIdEither : (ea : Either e a) -> map Prelude.id ea = ea
mapIdEither $ Left err  = Refl
mapIdEither $ Right val = Refl

mapIdList : (la : List a) -> map Prelude.id la = la
mapIdList Nil       = Refl
mapIdList (x :: xs) = cong (x ::) $ mapIdList xs

replaceVect : (ix : Fin n) -> a -> Vect n a -> Vect n a
replaceVect FZ     y (x :: xs) = y :: xs
replaceVect (FS k) y (x :: xs) = x :: replaceVect k y xs

replaceIndex :  (ix : Fin n)
             -> (v : a)
             -> (as : Vect n a)
             -> index ix (replaceVect ix v as) = v
replaceIndex FZ     y (x :: xs) = Refl
replaceIndex (FS k) y (x :: xs) = replaceIndex k y xs

insertVect : (ix : Fin (S n)) -> a -> Vect n a -> Vect (S n) a
insertVect FZ     y xs        = y :: xs
insertVect (FS k) y (x :: xs) = x :: insertVect k y xs

insertIndex :  (ix : Fin (S n))
            -> (v : a)
            -> (as : Vect n a)
            -> index ix (insertVect ix v as) = v
insertIndex FZ     y xs        = Refl
insertIndex (FS k) y (x :: xs) = insertIndex k y xs



--  *** Exercises 3 ***



Uninhabited (Vect (S n) Void) where
  uninhabited (_ :: _) impossible

Uninhabited a => Uninhabited (Vect (S n) a) where
  uninhabited = uninhabited . head

contraSym : ((0 _ : a = b) -> Void) -> Not (b = a)
contraSym contra Refl = contra Refl

notSym : Not (a = b) -> Not (b = a)
notSym f prf = f $ sym prf

contraTrans : (0 _ : a = b) -> ((0 _ : b = c) -> Void) -> Not (a = c)
contraTrans Refl contra Refl = contra Refl

notTrans : a = b -> Not (b = c) -> Not (a = c)
notTrans ab f ac = f $ trans (sym ab) ac

data Crud : (i, a : Type) -> Type where
  Create : (value : a) -> Crud i a
  Update : (id : i) -> (value : a) -> Crud i a
  Read   : (id : i) -> Crud i a
  Delete : (id : i) -> Crud i a

Uninhabited a => Uninhabited i => Uninhabited (Crud i a) where
  uninhabited (Create value)    = uninhabited value
  uninhabited (Update id value) = uninhabited value
  uninhabited (Read id)         = uninhabited id
  uninhabited (Delete id)       = uninhabited id

ctNat : ColType -> Nat
ctNat I64     = Z
ctNat Str     = S Z
ctNat Boolean = S (S Z)
ctNat Float   = S (S (S Z))

ctNatInjective :  (c1,c2 : ColType) -> ctNat c1 = ctNat c2 -> c1 = c2
ctNatInjective I64     I64     Refl = Refl
ctNatInjective Str     Str     Refl = Refl
ctNatInjective Boolean Boolean Refl = Refl
ctNatInjective Float   Float   Refl = Refl

namespace DecEqColType
  public export
  DecEq ColType where
    decEq c1 c2 = case decEq (ctNat c1) (ctNat c2) of
      Yes prf   => Yes $ ctNatInjective c1 c2 prf
      No contra => No $ \x => contra $ cong ctNat x 



--  *** Exercises 4 ***



plusSuccRightSucc' :  (left : Nat)
                   -> (right : Nat)
                   -> S (left + right) = left + (S right)
plusSuccRightSucc' Z     j = Refl
plusSuccRightSucc' (S k) j = cong S $ plusSuccRightSucc' k j

minusNNZ : (n : Nat) -> minus n n = Z
minusNNZ Z     = Refl
minusNNZ (S k) = minusNNZ k

minusNZZ : (n : Nat) -> minus n Z = n
minusNZZ Z     = Refl
minusNZZ (S k) = Refl

multNSZN : (n : Nat) -> n * (S Z) = n
multNSZN Z     = Refl
multNSZN (S k) = cong S $ multNSZN k

multSZNN : (n : Nat) -> (S Z) * n = n
multSZNN Z     = Refl
multSZNN (S k) = cong S $ multSZNN k

plusNatComm : (m,n : Nat) -> m + n = n + m
plusNatComm Z     n = rewrite addZeroRight n in Refl
plusNatComm (S k) n =
  rewrite sym $ plusSuccRightSucc' n k
  in cong S $ plusNatComm k n

mapVectTR : (f : a -> b) -> Vect n a -> Vect n b
mapVectTR f = go Nil
  where go : Vect l b -> Vect m a -> Vect (l + m) b
        go acc Nil       = rewrite (addZeroRight l) in acc
        go {m = S k}
           acc (x :: xs) =
             rewrite sym $ plusSuccRightSucc' l k
             in go (snoc acc (f x)) xs

mapAppend' :  (f : a -> b)
           -> (xs : List a)
           -> (ys : List a)
           -> map f (xs ++ ys) = map f xs ++ map f ys
mapAppend' f Nil       ys = Refl
mapAppend' f (x :: xs) ys = cong (f x ::) $ mapAppend' f xs ys

zipTables' : Table -> Table -> Maybe Table
zipTables' (MkTable s1 m rs1) (MkTable s2 n rs2) = case decEq m n of
  Yes Refl =>
    let res = zipWith (++) rs1 rs2
     in Just $ MkTable (s1 ++ s2) n (rewrite mapAppend' IdrisType s1 s2 in res)
  No  _    => Nothing

zipTables'' : Table -> Table -> Maybe Table
zipTables'' (MkTable s1 m rs1) (MkTable s2 n rs2) = case decEq m n of
  Yes Refl => ?lhs
  No  c    => Nothing

zipTables''' : Table -> Table -> Maybe Table
zipTables''' (MkTable s1 m rs1) (MkTable s2 n rs2) = case eqNat m n of
  Just Refl =>
    let res = zipWith (++) rs1 rs2
     in Just $ MkTable (s1 ++ s2) n (rewrite mapAppend' IdrisType s1 s2 in res)
  Nothing   => Nothing

