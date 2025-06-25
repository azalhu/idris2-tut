module Tutorial.TutEq

import Data.Either
import Data.HVect
import Data.Vect
import Data.String

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

data SameColType : (c1, c2 : ColType) -> Type where
  SameCT : SameColType c c

record Schema where
  constructor MkSchema
  len  : Nat
  cols : Vect len ColType

namespace SchemaUtils
  export
  Nil : Schema
  Nil = MkSchema Z Nil

  export
  (::) : ColType -> Schema -> Schema
  (::) ct (MkSchema k cts) = MkSchema (S k) (ct :: cts)

  export
  (++) : Schema -> Schema -> Schema
  (++) (MkSchema n1 c1) (MkSchema n2 c2) = MkSchema (n1 + n2) (c1 ++ c2)

data SameSchema : (s1, s2 : Schema) -> Type where
  Same : SameSchema s s

IdrisType : ColType -> Type
IdrisType I64     = Int64
IdrisType Str     = String
IdrisType Boolean = Bool
IdrisType Float   = Double

Row : Schema -> Type
Row schema = HVect schema.len $ map IdrisType schema.cols

record Table where
  constructor MkTable
  schema : Schema
  size   : Nat
  rows   : Vect size $ Row schema



--  *** Core Functionality ***



sameColType : (c1, c2 : ColType) -> Maybe (SameColType c1 c2)
sameColType I64     I64     = Just SameCT
sameColType Str     Str     = Just SameCT
sameColType Boolean Boolean = Just SameCT
sameColType Float   Float   = Just SameCT
sameColType I64     _       = Nothing
sameColType Str     _       = Nothing
sameColType Boolean _       = Nothing
sameColType Float   _       = Nothing

sameNil : SameSchema (MkSchema _ Nil) (MkSchema _ Nil)
sameNil = Same

sameCons :  SameColType c1 c2
         -> SameSchema (MkSchema _ s1) (MkSchema _ s2)
         -> SameSchema (MkSchema _ (c1 :: s1)) (MkSchema _ (c2 :: s2))
sameCons SameCT Same = Same

sameSchema : (s1, s2 : Schema) -> Maybe (SameSchema s1 s2)
sameSchema (MkSchema _ Nil)       (MkSchema _ Nil)       = Just Same
sameSchema (MkSchema _ (x :: xs)) (MkSchema _ (y :: ys)) =
  [| sameCons (sameColType x y) (sameSchema (MkSchema _ xs) (MkSchema _ ys)) |]
sameSchema (MkSchema _ (x :: xs)) (MkSchema _ Nil)       = Nothing
sameSchema (MkSchema _ Nil)       (MkSchema _ (y :: ys)) = Nothing

concatTables1 : Table -> Table -> Maybe Table
concatTables1 (MkTable s1 _ rs1) (MkTable s2 _ rs2) = case sameSchema s1 s2 of
  Just Same => Just $ MkTable s1 _ (rs1 ++ rs2)
  Nothing   => Nothing

eqColType : (c1, c2 : ColType) -> Maybe (c1 = c2)
eqColType I64     I64     = Just Refl
eqColType Str     Str     = Just Refl
eqColType Boolean Boolean = Just Refl
eqColType Float   Float   = Just Refl
eqColType I64     _       = Nothing
eqColType Str     _       = Nothing
eqColType Boolean _       = Nothing
eqColType Float   _       = Nothing

eqS :  {0 n1,n2 : Nat}
    -> n1 = n2
    -> S n1 = S n2
eqS Refl = Refl

eqLen : (n1, n2 : Nat) -> Maybe (n1 = n2)
eqLen Z     Z     = Just Refl
eqLen Z     (S k) = Nothing
eqLen (S k) Z     = Nothing
eqLen (S k) (S j) = [| eqS (eqLen k j) |]

eqCons :  {0 c1,c2 : ColType}
       -> {0 v1 : Vect n1 ColType}
       -> {0 v2 : Vect n2 ColType}
       -> c1 = c2
       -> n1 = n2
       -> v1 = v2
       -> c1 :: v1 = c2 :: v2
eqCons Refl Refl Refl = Refl

eqColTypes :  {m,n : Nat}
           -> (v1 : Vect m ColType)
           -> (v2 : Vect n ColType)
           -> Maybe (v1 = v2)
eqColTypes Nil       Nil       = Just Refl
eqColTypes (_ :: _)  Nil       = Nothing
eqColTypes Nil       (_ :: _)  = Nothing
eqColTypes {m = S k} {n = S j}
           (x :: xs) (y :: ys) =
  [| eqCons (eqColType x y) (eqLen k j) (eqColTypes xs ys) |]

eqSch :  {0 s1 : Vect n1 ColType}
      -> {0 s2 : Vect n2 ColType}
      -> s1 = s2
      -> MkSchema n1 s1 = MkSchema n2 s2
eqSch Refl = Refl

eqSchema : (s1,s2 : Schema) -> Maybe (s1 = s2)
eqSchema (MkSchema _ Nil)      (MkSchema _ Nil)      = Just Refl
eqSchema (MkSchema _ (_ :: _)) (MkSchema _ Nil)      = Nothing
eqSchema (MkSchema _ Nil)      (MkSchema _ (_ :: _)) = Nothing
eqSchema (MkSchema m xs)       (MkSchema n ys)       =
  [| eqSch (eqColTypes xs ys) |]



--  *** Exercises 1 ***



sctReflexive : SameColType c1 c1
sctReflexive = SameCT

sctSymmetric : SameColType c1 c2 -> SameColType c2 c1
sctSymmetric SameCT = SameCT

sctTransitive : SameColType c1 c2 -> SameColType c2 c3 -> SameColType c1 c3
sctTransitive SameCT SameCT = SameCT

sctCongruent :  {0 f : ColType -> ColType}
             -> SameColType c1 c2
             -> SameColType (f c1) (f c2)
sctCongruent SameCT = SameCT

sym' : (0 _ : x = y) -> y = x
sym' Refl = Refl

trans' : (0 _ : a = b) -> (0 _ : b = c) -> a = c
trans' Refl Refl = Refl

cong' : (0 f : (t -> u)) -> (0 _ : a = b) -> f a = f b
cong' _ Refl = Refl

eqNat : (m,n : Nat) -> Maybe (m = n)
eqNat Z     Z     = Just Refl
eqNat Z     (S _) = Nothing
eqNat (S k) Z     = Nothing
eqNat (S k) (S j) = (\x => cong S x) <$> eqNat k j

eqRowLens : {ts1 : _} -> {ts2 : _} -> Row ts1 -> Row ts2 -> (n : Nat ** n = ts1.len + ts2.len)
eqRowLens {ts1 = MkSchema l xs} {ts2 = MkSchema m ys}
          _ _ = (l + m ** Refl)

appRows : {ts1 : _} -> {ts2 : _} -> Row ts1 -> Row ts2 -> Row (ts1 ++ ts2)
appRows {ts1 = MkSchema _ Nil} {ts2 = MkSchema n ys}
        Nil      y = ?lhsAppRows
appRows {ts1 = MkSchema _ (_ :: _)}
        (h :: t) y = ?rhsAppRows

zip : Table -> Table -> Maybe Table
zip (MkTable schema1 size1 rows1) (MkTable schema2 size2 rows2) =
  case eqNat size1 size2 of
    Just Refl => Just $ MkTable _ _ (zipWith appRows rows1 rows2)
    Nothing   => Nothing



--  *** Programs as Proofs ***



onePlusOne : the Nat 1 + 1 = 2
onePlusOne = Refl

onePlusOneWrong : the Nat 1 + 1 = 3

mapListLength : (f : a -> b) -> (as : List a) -> length as = length (map f as)
mapListLength _ Nil       = Refl
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

mapMaybeId1 : (ma : Maybe a) -> map Prelude.id ma = ma
mapMaybeId1 Nothing  = Refl
mapMaybeId1 (Just x) = Refl



--  *** Exercises 2 ***



mapEitherId : (eea : Either e a) -> map Prelude.id eea = eea
mapEitherId (Left  err) = Refl
mapEitherId (Right val) = Refl

mapListId : (la : List a) -> map Prelude.id la = la
mapListId Nil       = Refl
mapListId (x :: xs) = cong (x ::) $ mapListId xs

replaceVect : (ix : Fin n) -> a -> Vect n a -> Vect n a
replaceVect FZ     y (_ :: xs) = y :: xs
replaceVect (FS k) y (x :: xs) = x :: replaceVect k y xs

indexReplace :  (ix : Fin n)
             -> (v : a)
             -> (as : Vect n a)
             -> index ix (replaceVect ix v as) = v
indexReplace FZ     y (x :: _)  = Refl
indexReplace (FS k) y (_ :: xs) = indexReplace k y xs

insertVect : (ix : Fin (S n)) -> a -> Vect n a -> Vect (S n) a
insertVect FZ     y xs        = y :: xs
insertVect (FS k) y (x :: xs) = x :: insertVect k y xs

indexInsert :  (ix : Fin (S n))
            -> (v : a)
            -> (as : Vect n a)
            -> index ix (insertVect ix v as) = v
indexInsert FZ     y xs        = Refl
indexInsert (FS k) y (_ :: xs) = indexInsert k y xs



--  *** Into the Void ***



onePlusOneWrongProvably : the Nat 1 + 1 = 3 -> Void
onePlusOneWrongProvably Refl impossible

notSameLength1 : (List.length as = length bs -> Void) -> as = bs -> Void
notSameLength1 f prf = f (cong length prf)

notSameLength : Not (List.length as = length bs) -> Not (as = bs)
notSameLength f prf = f (cong length prf)

contraCong : {0 f : _} -> Not (f a = f b) -> Not (a = b)
contraCong fun x = fun $ cong f x

Uninhabited (SameColType I64 Str) where
  uninhabited SameCT impossible

Uninhabited (SameSchema Nil (h :: t)) where
  uninhabited = ?uninhabited_same_schema

Uninhabited (MkSchema _ Nil = MkSchema _ (h :: t)) where
  uninhabited Refl impossible

Uninhabited (MkSchema _ (h :: t) = MkSchema _ Nil) where
  uninhabited Refl impossible

