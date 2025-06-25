module Tutorial.TutPredicates

import Data.Either
import Data.List1
import Data.String
import Data.Vect
import Data.HList
import Decidable.Equality

import Text.CSV
import System.File

%default total



--  ****** Preconditions ******



--  *** Example: Non-empty Lists ***



data NotNil : (as : List a) -> Type where
  IsNotNil : NotNil (h :: t)

head1 : (as : List a) -> (0 _ : NotNil as) -> a
head1 (h :: _) _ = h
head1 Nil      _ impossible

headEx1 : Nat
headEx1 = head1 [1,2,3] IsNotNil

head2 : (as : List a) -> {0 p : NotNil as} -> a
head2 (h :: _) = h
head2 Nil      impossible

headEx2 : Nat
headEx2 = head2 [1,2,3] {p = IsNotNil}

head3 : (as : List a) -> {auto 0 _ : NotNil as} -> a
head3 (h :: _) = h
head3 Nil      impossible

headEx3 : Nat
headEx3 = head3 [1,2,3]

Uninhabited (NotNil Nil) where
  uninhabited IsNotNil impossible

nonEmpty : (as : List a) -> Dec (NotNil as)
nonEmpty (h :: t) = Yes IsNotNil
nonEmpty Nil      = No uninhabited

headMaybe1 : List a -> Maybe a
headMaybe1 as = case nonEmpty as of
  Yes prf => Just $ head1 as prf
  No  _   => Nothing



--  *** Auto Implicits ***



replicate' : {n : _} -> a -> Vect n a
replicate' {n = Z}   _ = Nil
replicate' {n = S _} v = v :: replicate' v

replicateEx1 : Vect 3 Nat
replicateEx1 = replicate' 12

replicateEx2 : {n : _} -> Vect n Nat
replicateEx2 = replicate' 12

replicateEx3 : List Nat
replicateEx3 = toList $ replicate' {n = 17} 12

replicateEx4 : {n : Nat} -> List Nat
replicateEx4 = toList $ replicate' {n} 12

head : (as : List a) -> {auto 0 prf : NotNil as} -> a
head (h :: _) = h
head Nil      impossible

headEx4 : Nat
headEx4 = TutPredicates.head [1,2,3]

failing "Can't find an implementation for NotNil []."
  errHead : Nat
  errHead = TutPredicates.head Nil

head' : (as : List a) -> (0 _ : NotNil as) => a
head' (h :: _) = h
head' Nil      impossible

headMaybe : List a -> Maybe a
headMaybe as = case nonEmpty as of
  Yes _ => Just $ head as
  No  _ => Nothing



--  *** Exercises part 1 ***



tail : (as : List a) -> {auto 0 prf : NotNil as} -> List a
tail (_ :: t) = t
tail Nil      impossible

tail' : (as : List a) -> (0 _ : NotNil as) => List a
tail' (_ :: t) = t
tail' Nil      impossible

foldMap1 : Semigroup m => (a -> m) -> (as : List a) -> (0 _ : NotNil as) => m
foldMap1 f (x :: Nil)     = f x
foldMap1 f (x :: y :: xs) = f x <+> foldMap1 f (y :: xs)
foldMap1 f Nil            impossible

concat1 : Semigroup a => (as : List a) -> (0 _ : NotNil as) => a
concat1 = foldMap1 id

max1 : Ord a => (as : List a) -> (0 _ : NotNil as) => a
max1 (x :: Nil)     = x
max1 (x :: y :: xs) = max x $ max1 (y :: xs)
max1 Nil            impossible

min1 : Ord a => (as : List a) -> (0 _ : NotNil as) => a
min1 (x :: Nil)     = x
min1 (x :: y :: xs) = min x $ min1 (y :: xs)
min1 Nil            impossible

data Pos : Nat -> Type where
  IsPos : Pos (S k)

safeDiv : (m : Nat) -> (n : Nat) -> (0 _ : Pos n) => Nat
safeDiv m n = div m n
safeDiv m Z impossible

data Def : Maybe a -> Type where
  IsDef : Def $ Just a

just : (v : Maybe a) -> (0 _ : Def v) => a 
just $ Just v  = v
just $ Nothing impossible

Uninhabited (Def Nothing) where
  uninhabited IsDef impossible

nonNothing : (v : Maybe a) -> Dec (Def v)
nonNothing $ Just v  = Yes IsDef
nonNothing $ Nothing = No uninhabited

data EErr : Either e a -> Type where
  IsEErr : EErr (Left e)

data EVal : Either e a -> Type where
  IsEVal : EVal (Right a)

err : (v : Either e a) -> (0 _ : EErr v) => e
err $ Left  v = v
err $ Right v impossible

val : (v : Either e a) -> (0 _ : EVal v) => a
val $ Right v = v
val $ Left v  impossible

Uninhabited (EErr (Right a)) where
  uninhabited IsEErr impossible

nonEVal : (v : Either e a) -> Dec (EErr v)
nonEVal $ Left e  = Yes IsEErr
nonEVal $ Right a = No uninhabited

Uninhabited (EVal (Left e)) where
  uninhabited IsEVal impossible

nonEErr : (v : Either e a) -> Dec (EVal v)
nonEErr $ Right a = Yes IsEVal
nonEErr $ Left e  = No uninhabited



--  ****** Contracts between Values ******



--  *** The Elem Predicate ***



get' : (0 t : Type) -> HList ts -> t

voidAgain : Void
voidAgain = get' Void Nil

data Elem : (elem : a) -> (as : List a) -> Type where
  Here  : Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

Uninhabited (Elem v Nil) where
  uninhabited Here impossible
  uninhabited (There _) impossible

MyList : List Nat
MyList = [1,3,7,8,4,12]

oneElemMyList : Elem 1 MyList
oneElemMyList = Here

sevenElemMyList : Elem 7 MyList
sevenElemMyList = There $ There Here

get : (0 t : Type) -> HList ts -> (prf : Elem t ts) => t
get t (v :: vs) {prf = Here}    = v
get t (v :: vs) {prf = There p} = get t vs
get t Nil impossible

Tps : List Type
Tps = List.replicate 50 Nat ++ [Maybe String]

hlist : HList Tps
hlist = [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        , Nothing ]

%auto_implicit_depth 100
aMaybe : Maybe String
aMaybe = get _ hlist
%auto_implicit_depth 25

--notHere : Not (v = x) -> Not (
--
--neitherHereNorThere : Not (v = x) -> Not (Elem v xs) -> Not (Elem v (x :: xs))
--neitherHereNorThere c1 c2 = ?rhs
--
--decElemMyList : DecEq a => (v : a) -> (as : List a) -> Dec (Elem v as)
--decElemMyList v Nil       = No absurd
--decElemMyList v (x :: xs) = case decEq v x of
--  Yes Refl   => Yes Here
--  No  contra => case decElemMyList v xs of
--    Yes prf     => Yes $ There prf
--    No  contra' => No $ neitherHereNorThere contra contra'
--
--data FiveInit : List Integer -> Type where
--  IsFiveInit : FiveInit (5 :: t)
--
--Uninhabited (FiveInit Nil) where
--  uninhabited IsFiveInit impossible
--
--Not (x = (5 :: xs)) => Uninhabited (FiveInit x) where
--  uninhabited IsFiveInit impossible
--
--isFiveInit : (v : List Integer) -> Dec (FiveInit v)
--isFiveInit (5 :: xs) = Yes IsFiveInit
--isFiveInit (x :: xs) = ?rhs
--isFiveInit Nil       = No uninhabited



--  *** Use Case: A nicer Schema ***



data ColType = I64 | Str | Boolean | Float

IdrisType : ColType -> Type
IdrisType I64     = Int64
IdrisType Str     = String
IdrisType Boolean = Bool
IdrisType Float   = Double

record Column where
  constructor MkColumn
  name : String
  type : ColType

export
infixr 8 :>

(:>) : String -> ColType -> Column
(:>) = MkColumn

Schema : Type
Schema = List Column

Show ColType where
  show I64     = "I64"
  show Str     = "Str"
  show Boolean = "Boolean"
  show Float   = "Float"

Show Column where
  show (MkColumn n ct) = "\{n}:\{show ct}"

showSchema : Schema -> String
showSchema = joinBy "," . map show

EmployeeSchema : Schema
EmployeeSchema = [ "firstName"  :> Str
                 , "lastName"   :> Str
                 , "email"      :> Str
                 , "age"        :> I64
                 , "salary"     :> Float
                 , "management" :> Boolean
                 ]

data Row : Schema -> Type where
  Nil  : Row Nil
  (::) :  {0 name : String}
       -> {0 type : ColType}
       -> (v : IdrisType type)
       -> Row ss
       -> Row (name :> type :: ss)

0 Employee : Type
Employee = Row EmployeeSchema

hock : Employee
hock = [ "Stefan", "Höck", "hock@foo.com", 46, 5443.2, False ]

data InSchema :  (name    : String)
              -> (schema  : Schema)
              -> (colType : ColType)
              -> Type where
  [search name schema]
  IsHere  : InSchema n (n :> t :: ss) t
  IsThere : InSchema n ss t -> InSchema n (fld :: ss) t

Uninhabited (InSchema n Nil c) where
  uninhabited IsHere impossible
  uninhabited (IsThere _) impossible

getAt :  {0 ss : Schema}
      -> (name : String)
      -> (row  : Row ss)
      -> (prf  : InSchema name ss c)
      => IdrisType c
getAt name (v :: vs) {prf = IsHere}    = v
getAt name (v :: vs) {prf = IsThere p} = getAt name vs

shoeck : String
shoeck =  getAt "firstName" hock
       ++ " "
       ++ getAt "lastName" hock
       ++ ": "
       ++ show (getAt "age" hock)
       ++ " years old."

inSchema : (ss : Schema) -> (n : String) -> Maybe (c ** InSchema n ss c)
inSchema Nil                   _ = Nothing
inSchema (MkColumn cn t :: xs) n = case decEq cn n of
  Yes Refl   => Just (t ** IsHere)
  No  contra => case inSchema xs n of
    Just (t ** prf) => Just (t ** IsThere prf)
    Nothing         => Nothing



--  *** Exercises part 2 ***



decInSchema : (ss : Schema) -> (n : String) -> Dec (c ** InSchema n ss c)
decInSchema Nil n                   = No (\(_ ** prf) => uninhabited prf)
decInSchema (MkColumn cn t :: xs) n = case decEq cn n of
  Yes Refl   => Yes (t ** IsHere)
  No  contra => case decInSchema xs n of
    Yes (t ** prf) => Yes (t ** IsThere prf)
    No  contra'    => No $ \case (_ ** IsHere)    => contra Refl
                                 (t ** IsThere p) => contra' (t ** p)

updateAt :  (name  : String)
         -> (row   : Row ss)
         -> (prf   : InSchema name ss c)
         => (f : IdrisType c -> IdrisType c)
         -> Row ss
updateAt name (v :: vs) {prf = IsHere}    f = f v :: vs
updateAt name (v :: vs) {prf = IsThere p} f = v :: updateAt name vs f
updateAt name Nil f impossible

data Elems : (xs,ys : List a) -> Type where
  ENil   : Elems Nil ys
  EHere  : Elems xs ys -> Elems (x :: xs) (x :: ys)
  EThere : Elems xs ys -> Elems xs (y :: ys)

extract :  (0 s1 : Schema)
        -> (row : Row s2)
        -> (prf : Elems s1 s2)
        => Row s1
extract Nil      _         {prf = ENil}     = Nil
extract (_ :: t) (v :: vs) {prf = EHere x}  = v :: extract t vs
extract s1       (v :: vs) {prf = EThere x} = extract s1 vs

namespace AllInSchema
  public export
  data AllInSchema :  (names : List String)
                   -> (schema : Schema)
                   -> (result : Schema)
                   -> Type where
    [search names schema]
    Nil  :  AllInSchema Nil s Nil
    (::) :  InSchema n s c
         -> AllInSchema ns s res
         -> AllInSchema (n :: ns) s (n :> c :: res)

  getAll :  {0 ss  : Schema}
         -> (names : List String)
         -> (row   : Row ss)
         -> (prf   : AllInSchema names ss res)
         => Row res
  getAll Nil       _   {prf = Nil}    = Nil
  getAll (n :: ns) row {prf = _ :: _} = getAt n row :: getAll ns row



--  ****** Use Case: Flexible Error Handling ******



record NoNat where
  constructor MkNoNat
  str : String

readNat' : String -> Either NoNat Nat
readNat' s = maybeToEither (MkNoNat s) $ parsePositive s

record NoColType where
  constructor MkNoColType
  str : String

readColType' : String -> Either NoColType ColType
readColType' "I64"     = Right I64
readColType' "Str"     = Right Str
readColType' "Boolean" = Right Boolean
readColType' "Float"   = Right Float
readColType' s         = Left $ MkNoColType s

record OutOfBounds where
  constructor MkOutOfBounds
  size  : Nat
  index : Nat

readFin' : {n : _} -> String -> Either (Either NoNat OutOfBounds) (Fin n)
readFin' s = do
  ix <- mapFst Left (readNat' s)
  maybeToEither (Right $ MkOutOfBounds n ix) $ natToFin ix n

data Sum : List Type -> Type where
  MkSum : (val : t) -> Sum ts

data Has : (v : a) -> (vs : Vect n a) -> Type where
  Z : Has v (v :: vs)
  S : Has v vs -> Has v (w :: vs)

Uninhabited (Has v Nil) where
  uninhabited Z impossible
  uninhabited (S _) impossible

data Union : Vect n Type -> Type where
  U : (ix : Has t ts) -> (val : t) -> Union ts

Uninhabited (Union Nil) where
  uninhabited (U ix _) = absurd ix

0 Err : Vect n Type -> Type -> Type
Err ts t = Either (Union ts) t

inject : (prf : Has t ts) => (v : t) -> Union ts
inject v = U %search v

fail : Has t ts => (err : t) -> Err ts a
fail err = Left $ inject err

failMaybe : Has t ts => (err : Lazy t) -> Maybe a -> Err ts a
failMaybe err = maybeToEither (inject err)

readNat : Has NoNat ts => String -> Err ts Nat
readNat s = failMaybe (MkNoNat s) $ parsePositive s

readColType : Has NoColType ts => String -> Err ts ColType
readColType "I64"     = Right I64
readColType "Str"     = Right Str
readColType "Boolean" = Right Boolean
readColType "Float"   = Right Float
readColType s         = fail $ MkNoColType s

0 Errs : List Type -> Vect n Type -> Type
Errs Nil       _  = ()
Errs (x :: xs) ts = (Has x ts, Errs xs ts)

readFin : {n : _} -> Errs [NoNat, OutOfBounds] ts => String -> Err ts (Fin n)
readFin s = do
  S ix <- readNat s | Z => fail (MkOutOfBounds n Z)
  failMaybe (MkOutOfBounds n (S ix)) $ natToFin ix n

fromCSV : String -> List String
fromCSV = forget . split (',' ==)

record InvalidColumn where
  constructor MkInvalidColumn
  str : String

readColumn : Errs [InvalidColumn, NoColType] ts => String -> Err ts Column
readColumn s = case forget $ split (':' ==) s of
  [n,ct] => MkColumn n <$> readColType ct
  _      => fail $ MkInvalidColumn s

readSchema : Errs [InvalidColumn, NoColType] ts => String -> Err ts Schema
readSchema = traverse readColumn . fromCSV

data RowError : Type where
  InvalidField  : (row, col : Nat) -> (ct : ColType) -> String -> RowError
  UnexpectedEOI : (row, col : Nat) -> RowError
  ExpectedEOI   : (row, col : Nat) -> RowError

decodeField :  Has RowError ts
            => (row,col : Nat)
            -> (c : ColType)
            -> String
            -> Err ts (IdrisType c)
decodeField row col c s =
  let err = InvalidField row col c s
   in case c of
        I64     => failMaybe err $ read s
        Str     => failMaybe err $ read s
        Boolean => failMaybe err $ read s
        Float   => failMaybe err $ read s

decodeRow :  Has RowError ts
          => {s : _}
          -> (row : Nat)
          -> (str : String)
          -> Err ts (Row s)
decodeRow row = go (S Z) s . fromCSV
  where go : Nat -> (cs : Schema) -> List String -> Err ts (Row cs)
        go k Nil                  Nil       = Right Nil
        go k Nil                  (_ :: _)  = fail $ ExpectedEOI row k
        go k (_ :: _)             Nil       = fail $ UnexpectedEOI row k
        go k (MkColumn n c :: cs) (s :: ss) =
          [| decodeField row k c s :: go (S k) cs ss |]



--  *** Error Handling ***



data Rem : (v : a) -> (vs : Vect (S n) a) -> (rem : Vect n a) -> Type where
  [search v vs]
  RZ : Rem v (v :: rem) rem
  RS : Rem v vs rem -> Rem v (w :: vs) (w :: rem)

-- TODO: wtf?
split : (prf : Rem t ts rem) => Union ts -> Either t (Union rem)
split {prf = RZ}   (U Z     val) = Left val
split {prf = RZ}   (U (S x) val) = Right (U x val)
split {prf = RS p} (U Z     val) = Right (U Z val)
split {prf = RS p} (U (S x) val) = case split {prf = p} (U x val) of
  Left  vt       => Left vt
  Right (U ix y) => Right $ U (S ix) y

handle :  Applicative f
       => Rem t ts rem
       => (h : t -> f a)
       -> Err ts a
       -> f (Err rem a)
handle h (Left x)  = case split x of
  Left  v   => Right <$> h v
  Right err => pure $ Left err
handle _ (Right x) = pure $ Right x

namespace Handler
  public export
  data Handler : (ts : Vect n Type) -> (a : Type) -> Type where
    Nil  : Handler Nil a
    (::) : (t -> a) -> Handler ts a -> Handler (t :: ts) a

  public export
  extract : Handler ts a -> Has t ts -> t -> a
  extract (f :: _)  Z     val = f val
  extract (_ :: fs) (S y) val = extract fs y val
  extract Nil       ix    _   = absurd ix

  public export
  handleAll : Applicative f => Handler ts (f a) -> Err ts a -> f a
  handleAll _ (Right v)       = pure v
  handleAll h (Left $ U ix v) = extract h ix v



--  *** Exercises part 3 ***



project : (0 t : Type) -> (prf : Has t ts) => Union ts -> Maybe t
project t {prf = Z}   (U Z val)     = Just val
project t {prf = S p} (U (S x) val) = project t (U x val)
project t {prf = Z}   (U (S x) val) = Nothing
project t {prf = S p} (U Z val)     = Nothing

project1 : Union [t] -> t
project1 (U Z val) = val
project1 (U (S x) val) = absurd x

safe : Err Nil a -> a
safe $ Right v = v
safe $ Left e  = absurd e

weakenHas : Has t ts -> Has t (ts ++ ss)
weakenHas Z     = Z
weakenHas (S x) = S $ weakenHas x

weaken : Union ts -> Union (ts ++ ss)
weaken (U ix val) = U (weakenHas ix) val

extendHas : {m : _} -> {0 pre : Vect m _} -> Has t ts -> Has t (pre ++ ts)
extendHas {m = Z}   {pre = Nil}    x = x
extendHas {m = S p} {pre = _ :: _} x = S $ extendHas x

extend : {m : _} -> {0 pre : Vect m _} -> Union ts -> Union (pre ++ ts)
extend (U ix val) = U (extendHas ix) val

0 ErrsV : Vect m Type -> Vect n Type -> Type
ErrsV Nil       _  = ()
ErrsV (x :: xs) ts = (Has x ts, ErrsV xs ts)

embed : (prf : ErrsV ts ss) => Union ts -> Union ss
embed (U Z val)     = inject val
embed (U (S x) val) = embed (U x val)

embedTest :  Err [NoNat, NoColType] a
          -> Err [FileError, NoColType, OutOfBounds, NoNat] a
embedTest = mapFst embed

handle' :  Applicative f
        => Rem t ts rem
        => (h : t -> f (Err rem a))
        -> Err ts a
        -> f (Err rem a)
handle' h (Left x)  = case split x of
  Left  v   => h v
  Right err => pure $ Left err
handle' _ (Right x) = pure $ Right x



--  ****** The Truth about Interfaces ******



isElem1 : Eq a => a -> List a -> Bool
isElem1 v Nil       = False
isElem1 v (x :: xs) = x == v || isElem1 v xs

isElem2 : {auto _ : Eq a} -> a -> List a -> Bool
isElem2 v Nil       = False
isElem2 v (x :: xs) = x == v || isElem2 v xs

eq : Eq a -> a -> a -> Bool
eq (MkEq feq fneq) = feq



--  *** A manual Interface Definition ***



record Print a where
  constructor MkPrint
  print' : a -> String

print0 : Print a -> a -> String
print0 = print'

print : Print a => a -> String
print = print' %search

print2 : (impl : Print a) => a -> String
print2 = print' impl

print3 : {auto impl : Print a} -> a -> String
print3 = print' impl

%hint
noNatPrint : Print NoNat
noNatPrint = MkPrint $ \e => "Not a natural number: \{e.str}"

%hint
noColTypePrint : Print NoColType
noColTypePrint = MkPrint $ \e => "Not a column type: \{e.str}"

%hint
outOfBoundsPrint : Print OutOfBounds
outOfBoundsPrint = MkPrint $ \e => "Index is out of bounds: \{show e.index}"

%hint
rowErrorPrint : Print RowError
rowErrorPrint = MkPrint $
  \case InvalidField r c ct s =>
          "Not a \{show ct} in row \{show r}, column \{show c}. \{s}"
        UnexpectedEOI r c =>
          "Unexpected end of input in row \{show r}, column \{show c}."
        ExpectedEOI r c =>
          "Expected end of input in row \{show r}, column \{show c}."

0 All : (f : a -> Type) -> Vect n a -> Type
All f Nil       = ()
All f (x :: xs) = (f x, All f xs)

unionPrintImpl : All Print ts => Union ts -> String
unionPrintImpl (U Z val)     = print val
unionPrintImpl (U (S x) val) = unionPrintImpl $ U x val

%hint
unionPrint : All Print ts => Print (Union ts)
unionPrint = MkPrint unionPrintImpl



--  Parsing CSV Commands



record Table where
  constructor MkTable
  schema : Schema
  size   : Nat
  rows   : Vect size (Row schema)

data Command : (t : Table) -> Type where
  PrintSchema :  Command t
  PrintSize   :  Command t
  New         :  (newSchema : Schema) -> Command t
  Prepend     :  Row t.schema -> Command t
  Get         :  Fin t.size -> Command t
  Delete      :  Fin t.size -> Command t
  Col         :  (name : String)
              -> (tpe  : ColType)
              -> (prf  : InSchema name t.schema tpe)
              -> Command t
  Quit        :  Command t

applyCommand : (t : Table) -> Command t -> Table
applyCommand t                 PrintSchema = t
applyCommand t                 PrintSize   = t
applyCommand t                 (New ts)    = MkTable ts Z Nil
applyCommand (MkTable ts n rs) (Prepend r) = MkTable ts (S n) $ r :: rs
applyCommand t                 (Get x)     = t
applyCommand t                 Quit        = t
applyCommand t                 (Col n c p) = t
applyCommand (MkTable ts n rs) (Delete x)  = case n of
  S k => MkTable ts k (deleteAt x rs)
  Z   => absurd x

record UnknownCommand where
  constructor MkUnknownCommand
  str : String

%hint
unknownCommandPrint : Print UnknownCommand
unknownCommandPrint = MkPrint $ \v => "Unknown command: \{v.str}"

record NoColName where
  constructor MkNoColName
  str : String

%hint
noColNamePrint : Print NoColName
noColNamePrint = MkPrint $ \v => "Unknown column: \{v.str}"

0 CmdErrs : Vect 7 Type
CmdErrs = [ InvalidColumn
          , NoColName
          , NoColType
          , NoNat
          , OutOfBounds
          , RowError
          , UnknownCommand ]

readCommand : (t : Table) -> String -> Err CmdErrs (Command t)
readCommand t                 "schema"  = Right PrintSchema
readCommand t                 "size"    = Right PrintSize
readCommand t                 "quit"    = Right Quit
readCommand (MkTable ts n rs) s         = case words s of
  ["new",    str] => New     <$> readSchema str
  "add" ::   ss   => Prepend <$> decodeRow 1 (unwords ss)
  ["get",    str] => Get     <$> readFin str
  ["delete", str] => Delete  <$> readFin str
  ["column", str] => case inSchema ts str of
    Just (ct ** prf) => Right $ Col str ct prf
    Nothing          => fail $ MkNoColName str
  _               => fail $ MkUnknownCommand s

encodeField : (t : ColType) -> IdrisType t -> String
encodeField I64     x     = show x
encodeField Str     x     = show x
encodeField Boolean True  = "t"
encodeField Boolean False = "f"
encodeField Float   x     = show x

encodeRow : (s : Schema) -> Row s -> String
encodeRow s = concat . intersperse "," . go s
  where go : (s' : Schema) -> Row s' -> Vect (length s') String
        go Nil                  Nil       = Nil
        go (MkColumn n c :: cs) (v :: vs) = encodeField c v :: go cs vs

encodeCol :  (name : String)
          -> (c    : ColType)
          -> InSchema name s c
          => Vect n (Row s)
          -> String
encodeCol name c = unlines . toList . map (\r => encodeField c $ getAt name r)

result : (t : Table) -> Command t -> String
result t PrintSchema   = "Current schema: \{showSchema t.schema}"
result t PrintSize     = "Current size: \{show t.size}"
result t (New ts)      = "Created table. Schema: \{showSchema ts}"
result t (Prepend r)   = "Row prepended: \{encodeRow t.schema r}"
result t (Delete x)    = "Deleted row: \{show $ FS x}."
result t Quit          = "Goodbye."
result t (Col n c prf) = "Column \{n}:\n\{encodeCol n c t.rows}"
result t (Get x)       =
  "Row \{show $ FS x}: \{encodeRow t.schema (index x t.rows)}"

covering
runProg : Table -> IO ()
runProg t = do
  putStr "Enter a command: "
  str <- getLine
  case readCommand t str of
    Left err   => putStrLn (print err) >> runProg t
    Right Quit => putStrLn (result t Quit)
    Right cmd  => putStrLn (result t cmd) >>
                  runProg (applyCommand t cmd)

covering
main : IO ()
main = runProg $ MkTable Nil Z Nil

