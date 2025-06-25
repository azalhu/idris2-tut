module Data.HVect

import Data.Fin
import Data.Vect

%default total

public export
data HVect : (n : Nat) -> (ts : Vect n Type) -> Type where
  Nil  : HVect Z Nil
  (::) : (v : t) -> (vs : HVect k ts) -> HVect (S k) (t :: ts)

public export
len : HVect n ts -> (m : Nat ** m = n)
len Nil       = (Z ** Refl)
len (_ :: ts) =
  let (l ** Refl) = len ts
   in (S l ** Refl)

public export
head : HVect _ (t :: _) -> t
head (v :: _) = v

public export
tail : HVect _ (_ :: ts) -> HVect _ ts
tail (_ :: vs) = vs

public export
(++) : HVect m xs -> HVect n ys -> HVect (m + n) (xs ++ ys)
Nil       ++ ws = ws
(v :: vs) ++ ws = v :: vs ++ ws

public export
indexVect : (as : Vect n a) -> Fin n -> a
indexVect (x :: _)  FZ     = x
indexVect (_ :: xs) (FS y) = indexVect xs y
indexVect Nil       _      impossible

public export
index : (ix : Fin n) -> HVect n ts -> indexVect ts ix
index FZ     (v :: _)  = v
index (FS x) (_ :: vs) = index x vs
index _      Nil       impossible

public export
data Sum : Nat -> Type where
  Add : (m : Nat) -> (n : Nat) -> Sum (m + n)

