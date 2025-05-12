module Tut

import Data.List
import Data.Vect

%default total

test : String
test = "Hello from Idris2!"

phi : (a : p -> q -> r) ->
      (b : y -> p) ->
      (c : y -> q) ->
      (x : y) -> r
phi a b c x = a (b x) (c x)

square : Integer -> Integer
square = phi (*) id id

twice : (Integer -> Integer) -> Integer -> Integer
twice = phi (.) id id

isEven : Integer -> Bool
isEven = ((==) 0) . (flip mod 2)

isOdd : Integer -> Bool
isOdd = not . isEven

isSquareOf : Integer -> Integer -> Bool
isSquareOf = flip $ (==) . square

isSmall : Integer -> Bool
isSmall = (<= 100)

absIsSmall : Integer -> Bool
absIsSmall = isSmall . abs

and : (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
and p1 p2 n = (p1 n) && (p2 n)

or : (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
or p1 p2 n = (p1 n) || (p2 n)

negate : (Integer -> Bool) -> Integer -> Bool
negate = (.) not

(&&) : (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
(&&) = and

(||) : (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
(||) = or

not : (Integer -> Bool) -> Integer -> Bool
not = negate

fib_rec : Nat -> Nat
fib_rec 0 = 0
fib_rec 1 = 1
fib_rec (S (S n)) = fib_rec (S n) + fib_rec n

covering
fib_rec' : Integer -> Integer
fib_rec' 0 = 0
fib_rec' 1 = 1
fib_rec' n = fib_rec' (n - 1) + fib_rec' (n - 2)

fib_iter : Nat -> Nat
fib_iter n = fib_tail_rec n 1 0 0
  where
    fib_tail_rec : Nat -> Nat -> Nat -> Nat -> Nat
    fib_tail_rec 0 _ _ acc = acc
    fib_tail_rec (S n) k j acc = fib_tail_rec n (k + j) k k

covering
fib_iter' : Integer -> Integer
fib_iter' n = fib_tail_rec n 1 0 0
  where
    fib_tail_rec : Integer -> Integer -> Integer -> Integer -> Integer
    fib_tail_rec 0 _ _ acc = acc
    fib_tail_rec n k j acc = fib_tail_rec (n - 1) (k + j) k k

private
infixr 4 >>>

(>>>) : (Bits8 -> Bits8) -> (Bits8 -> Bits8) -> Bits8 -> Bits8
(>>>) f1 f2 = f2 . f1

foo : Bits8 -> Bits8
foo n = 2 * n + 3

foo_test : Bits8 -> Bits8
foo_test = foo >>> foo >>> foo >>> foo

applyToTen : (Integer -> Integer) -> Integer
applyToTen f = f 10

main : IO ()
main = putStrLn test

namespace ADT.Enumerations
  export
  and : Bool -> Bool -> Bool
  and False _ = False
  and True b = b

  export
  or : Bool -> Bool -> Bool
  or True _ = True
  or False b = b

  export
  xor : Bool -> Bool -> Bool
  xor True = not
  xor False = id

  public export
  data UnitOfTime = Second
                  | Minute
                  | Hour
                  | Day
                  | Week

  export
  Show UnitOfTime where
    show Second = "Second"
    show Minute = "Minute"
    show Hour = "Hour"
    show Day = "Day"
    show Week = "Week"

  export
  Eq UnitOfTime where
    (==) Second Second = True
    (==) Minute Minute = True
    (==) Hour Hour = True
    (==) Day Day = True
    (==) Week Week = True
    (==) _ _ = False

  export
  Ord UnitOfTime where
    compare Second Second = EQ
    compare Second _ = LT
    compare Minute Second = GT
    compare Minute Minute = EQ
    compare Minute _ = LT
    compare Hour Second = GT
    compare Hour Minute = GT
    compare Hour Hour = EQ
    compare Hour _ = LT
    compare Day Week = LT
    compare Day Day = EQ
    compare Day _ = GT
    compare Week Week = EQ
    compare Week _ = GT

  export
  toSeconds : UnitOfTime -> Integer -> Integer
  toSeconds Second = id
  toSeconds Minute = (*) 60
  toSeconds Hour = (*) (60 * 60)
  toSeconds Day = (*) (24 * 60 * 60)
  toSeconds Week = (*) (7 * 24 * 60 * 60)

  export
  fromSeconds : UnitOfTime -> Integer -> Integer
  fromSeconds = flip div . flip toSeconds 1

  export
  convert : UnitOfTime -> Integer -> UnitOfTime -> Integer
  convert = flip fromSeconds .: toSeconds

  public export
  data ChemicalElement = H
                       | C
                       | N
                       | O
                       | F

  export
  atomicMass : {c : ChemicalElement} -> Double
  atomicMass {c=H} = 1.008
  atomicMass {c=C} = 12.011
  atomicMass {c=N} = 14.007
  atomicMass {c=O} = 15.999
  atomicMass {c=F} = 18.9984

namespace ADT.SumTypes
  public export
  data Title = Mr
             | Mrs
             | Other String

  export
  dr : Title
  dr = Other "Dr."

  export
  showTitle : Title -> String
  showTitle Mr = "Mr."
  showTitle Mrs = "Mrs."
  showTitle (Other t) = t

  export
  greet : Title -> String -> String
  greet t name = "Hello, \{showTitle t} \{name}!"

  export
  eqTitle : Title -> Title -> Bool
  eqTitle Mr Mr = True
  eqTitle Mrs Mrs = True
  eqTitle (Other t1) (Other t2) = t1 == t2
  eqTitle t1 (Other t2) = showTitle t1 == t2
  eqTitle (Other t1) t2 = t1 == showTitle t2
  eqTitle _ _ = False

  export
  isOther : Title -> Bool
  isOther (Other _) = True
  isOther _ = False

  public export
  data Credentials = Password String Bits64
                   | Key String String

  public export
  data LoginError = UnknownUsername String
                  | InvalidPassword
                  | InvalidKey

  export
  showError : LoginError -> String
  showError (UnknownUsername username) = "Unknown username: \{username}"
  showError InvalidPassword = "Invalid password"
  showError InvalidKey = "Invalid key"

namespace ADT.ProductTypes
  public export
  record User where
    constructor MkUser
    name : String
    title : Title
    age : Bits8

  export
  agentY : User
  agentY = MkUser "Y" (Other "Agent") 51

  export
  drNo : User
  drNo = MkUser "No" dr 73

  export
  greetUser : User -> String
  greetUser (MkUser n t _) = greet t n

  failing "Mismatch between: String and Title"
    greetUser' : User -> String
    greetUser' (MkUser n t _) = greet n t

  export
  incAge : User -> User
  incAge = { age $= (+ 1) }

  export
  drNoJunior : User
  drNoJunior = { name $= (++ " Jr."), title := Mr, age := 17 } drNo

  public export
  record TimeSpan where
    constructor MkTimeSpan
    unit : UnitOfTime
    duration : Integer

  export
  toSeconds : TimeSpan -> Integer
  toSeconds ts = toSeconds ts.unit ts.duration

  export
  isEqual : TimeSpan -> TimeSpan -> Bool
  isEqual = (==) `on` toSeconds

  export
  Show TimeSpan where
    show ts = "\{show ts.unit} (\{show (toSeconds ts)})"

  export
  add' : TimeSpan -> TimeSpan -> TimeSpan
  add' t1 t2 =
    let t1_seconds = toSeconds t1
        t2_seconds = toSeconds t2
        sum_seconds = t1_seconds + t2_seconds in
        if t1.unit < t2.unit
           then MkTimeSpan t1.unit (fromSeconds t1.unit sum_seconds)
           else MkTimeSpan t2.unit (fromSeconds t2.unit sum_seconds)

  export
  timeSpanToSeconds : TimeSpan -> Integer
  timeSpanToSeconds (MkTimeSpan unit duration) = toSeconds unit duration

  export
  eqTimeSpan : TimeSpan -> TimeSpan -> Bool
  eqTimeSpan = (==) `on` timeSpanToSeconds

  export
  showUnit : UnitOfTime -> String
  showUnit Second = "s"
  showUnit Minute = "min"
  showUnit Hour = "h"
  showUnit Day = "d"
  showUnit Week = "w"

  export
  prettyTimeSpan : TimeSpan -> String
  prettyTimeSpan (MkTimeSpan Second d) = show d ++ " s"
  prettyTimeSpan (MkTimeSpan u d) =
    show d ++ " " ++ showUnit u ++ "(" ++ show (toSeconds u d) ++ " s)"

  export
  compareUnit : UnitOfTime -> UnitOfTime -> Ordering
  compareUnit = compare `on` flip toSeconds 1

  export
  minUnit : UnitOfTime -> UnitOfTime -> UnitOfTime
  minUnit u1 u2 =
    case compareUnit u1 u2 of
         LT => u1
         _ => u2

  export
  addTimeSpan : TimeSpan -> TimeSpan -> TimeSpan
  addTimeSpan (MkTimeSpan u1 d1) (MkTimeSpan u2 d2) =
    let u = minUnit u1 u2 in
        MkTimeSpan u (convert u1 d1 u + convert u2 d2 u)

namespace ADT.GenericDataTypes
  data Weekday = Monday
               | Tuesday
               | Wednesday
               | Thursday
               | Friday
               | Saturday
               | Sunday

  public export
  data MaybeWeekday = WD Weekday | NoWeekday

  export
  readWeekday : String -> MaybeWeekday
  readWeekday "Monday" = WD Monday
  readWeekday "Tuesday" = WD Tuesday
  readWeekday "Wednesday" = WD Wednesday
  readWeekday "Thursday" = WD Thursday
  readWeekday "Friday" = WD Friday
  readWeekday "Saturday" = WD Saturday
  readWeekday "Sunday" = WD Sunday
  readWeekday _ = NoWeekday

  public export
  data Weird : Type -> Type where
    Bum : a -> Weird a

  export
  mapMaybe : (a -> b) -> Maybe a -> Maybe b
  mapMaybe f (Just a) = Just (f a)
  mapMaybe _ _ = Nothing

  export
  appMaybe : Maybe (a -> b) -> Maybe a -> Maybe b
  appMaybe (Just f) (Just a) = Just (f a)
  appMaybe _ _ = Nothing

  export
  bindMaybe : Maybe a -> (a -> Maybe b) -> Maybe b
  bindMaybe (Just a) f = f a
  bindMaybe _ _ = Nothing

  export
  filterMaybe : (a -> Bool) -> Maybe a -> Maybe a
  filterMaybe f (Just a) =
    if f a
       then Just a
       else Nothing
  filterMaybe _ _ = Nothing

  export
  first : Maybe a -> Maybe a -> Maybe a
  first f@(Just _) _ = f
  first _ l = l

  export
  last : Maybe a -> Maybe a -> Maybe a
  last _ l@(Just _) = l
  last f _ = f

  export
  foldMaybe : (acc -> el -> acc) -> acc -> Maybe el -> acc
  foldMaybe _ acc Nothing = acc
  foldMaybe f acc (Just el) = f acc el

  export
  mapEither : (a -> b) -> Either e a -> Either e b
  mapEither f (Right a) = Right (f a)
  mapEither _ (Left e) = Left e

  export
  appEither : Either e (a -> b) -> Either e a -> Either e b
  appEither (Right f) (Right a) = Right (f a)
  appEither (Left e) _ = Left e
  appEither _ (Left e) = Left e

  export
  bindEither : Either e a -> (a -> Either e b) -> Either e b
  bindEither (Right a) f = f a
  bindEither (Left e) _ = Left e

  export
  firstEither : (e -> e -> e) -> Either e a -> Either e a -> Either e a
  firstEither _ (Right a) _ = Right a
  firstEither _ _ (Right a) = Right a
  firstEither acc (Left e1) (Left e2) = Left (acc e1 e2)

  export
  lastEither : (e -> e -> e) -> Either e a -> Either e a -> Either e a
  lastEither _ _ (Right a) = Right a
  lastEither _ (Right a) _ = Right a
  lastEither acc (Left e1) (Left e2) = Left (acc e1 e2)

  export
  fromEither : (e -> c) -> (a -> c) -> Either e a -> c
  fromEither _ f (Right a) = f a
  fromEither f _ (Left e) = f e

  export
  mapList : (a -> b) -> List a -> List b
  mapList _ Nil = Nil
  mapList f (x :: xs) = f x :: mapList f xs

  export
  filterList : (a -> Bool) -> List a -> List a
  filterList _ Nil = Nil
  filterList p (x :: xs) = let xs' = filterList p xs in
                               case p x of
                                    True => x :: xs'
                                    False => xs'

  export
  headMaybe : List a -> Maybe a
  headMaybe Nil = Nothing
  headMaybe (x :: _) = Just x

  export
  tailMaybe : List a -> Maybe (List a)
  tailMaybe Nil = Nothing
  tailMaybe (_ :: xs) = Just xs

  export
  lastMaybe : List a -> Maybe a
  lastMaybe Nil = Nothing
  lastMaybe (x :: Nil) = Just x
  lastMaybe (_ :: xs) = lastMaybe xs

  export
  initMaybe : List a -> Maybe (List a)
  initMaybe Nil = Nothing
  initMaybe (x :: Nil) = Just [x]
  initMaybe (x :: xs) = let xs' = initMaybe xs in
                            case xs' of
                                 Nothing => Nothing
                                 Just xs' => Just (x :: xs')

  export
  foldList : (acc -> el -> acc) -> acc -> List el -> acc
  foldList _ acc Nil = acc
  foldList f acc (el :: els) = foldList f (f acc el) els

  public export
  record Client where
    constructor MkClient
    name : String
    title : Title
    age : Bits8
    passwordOrKey : Either Bits64 String

  export
  login : List Client -> Credentials -> Either LoginError Client
  login Nil _ = Left (UnknownUsername "User not found")
  login (c :: cs) cred@(Password username password) =
    case c.passwordOrKey of
         Left pw => if c.name == username && pw == password
                       then Right c
                       else login cs cred
         _ => login cs cred
  login (c :: cs) cred@(Key username key) =
    case c.passwordOrKey of
         Right k => if c.name == username && k == key
                       then Right c
                       else login cs cred
         _ => login cs cred

namespace Interfaces.Basics
  public export
  interface Comp a where
    comp : a -> a -> Ordering

  export
  implementation Comp Bits8 where
    comp = compare

  export
  implementation Comp Bits16 where
    comp = compare

  export
  implementation Comp Integer where
    comp = compare

  export
  lessThan : Comp a => a -> a -> Bool
  lessThan s1 s2 = LT == comp s1 s2

  export
  greaterThan : Comp a => a -> a -> Bool
  greaterThan s1 s2 = GT == comp s1 s2

  export
  minimum : Comp a => a -> a -> a
  minimum s1 s2 =
    case comp s1 s2 of
         LT => s1
         _ => s2

  export
  maximum : Comp a => a -> a -> a
  maximum s1 s2 =
    case comp s1 s2 of
         GT => s1
         _ => s2

  ||| S : x y z = x z (y z)
  s_comb : (x : a -> b -> c) ->
           (y : a -> b) ->
           (z : a) ->
           c
  s_comb x y z = x z (y z)

  ||| S1 : x y w z = x z (y w z)
  s1_comb : (x : a -> b -> d) ->
            (y : c -> a -> b) ->
            (w : c) ->
            (z : a) ->
            d
  s1_comb x y w z = x z (y w z)

  ||| S2 : x y w z = x z (y z w)
  s2_comb : (x : a -> b -> d) ->
            (y : a -> c -> b) ->
            (w : c) ->
            (z : a) ->
            d
  s2_comb x y w z = x z (y z w)

  ||| SX : x y z w = x w (z w) (S y w z)
  sx_comb : (x : a -> b -> c -> d) ->
            (y : a -> b -> c) ->
            (w : a -> b) ->
            (z : a) ->
            d
  sx_comb x y w z = x z (w z) (s_comb y w z)

  export
  anyLarger' : Comp a => a -> List a -> Bool
  anyLarger' = any . lessThan

  export
  anyLarger : Comp a => List a -> a -> Bool
  anyLarger = flip $ any . lessThan
  --anyLarger = (. lessThan) . flip any
  --anyLarger xs x = any (lessThan x) xs
  --anyLarger = s2_comb lessThan (foldl maximum)
  --anyLarger = s1_comb lessThan (flip (foldl maximum))
  --anyLarger = (s_comb lessThan) . flip (foldl maximum)
  --anyLarger xs = s_comb lessThan (flip (foldl maximum) xs)
  --anyLarger xs x = s_comb lessThan (flip (foldl maximum) xs) x
  --anyLarger xs x = lessThan x $ (flip (foldl maximum) xs) x
  --anyLarger xs x = lessThan x ((flip (foldl maximum) xs) x)
  --anyLarger xs x = lessThan x (flip (foldl maximum) xs x)
  --anyLarger xs x = lessThan x (foldl maximum x xs)
  --anyLarger xs x = greaterThan (foldl maximum x xs) x

  export
  allLarger' : Comp a => a -> List a -> Bool
  allLarger' = all . lessThan

  export
  allLarger : Comp a => List a -> a -> Bool
  allLarger = flip $ all . lessThan
  --allLarger = (. lessThan) . flip all
  --allLarger = ($) (flip (.) (flip (.)) (((.) flip (.) flip) all)) lessThan
  --allLarger xs x = all (lessThan x) xs

  export
  maxElem : Comp a => List a -> Maybe a
  maxElem Nil = Nothing
  maxElem xs@(_::_) = Just $ foldl1 maximum xs

  export
  minElem : Comp a => List a -> Maybe a
  minElem Nil = Nothing
  minElem xs@(_::_) = Just $ foldl1 minimum xs

  public export
  interface Concat a where
    concat : a -> a -> a

  export
  implementation Concat (List a) where
    concat = (++)

  export
  implementation Concat String where
    concat = (++)

  public export
  interface Concat a => Empty a where
    empty : a

  export
  implementation Empty (List a) where
    empty = Nil

  export
  implementation Empty String where
    empty = ""

  export
  concatList : Concat a => List a -> Maybe a
  concatList Nil = Nothing
  concatList xs@(_::_) = Just $ foldl1 concat xs

  export
  concatListE : Empty a => List a -> a
  concatListE xs = foldl concat empty xs

  export
  bluebird : (f : b -> c) ->
             (g : a -> b) ->
             (x : a) ->
             c
  bluebird = (.)

  export
  blackbird : (f : c -> d) ->
              (g : a -> b -> c) ->
              (x : a) ->
              (y : b) ->
              d
  blackbird = (.:)

  -- Failed attempts at applying S-combinator from existing function compositions,
  -- in order to define the function in a point-free style
  -- Remember NOT!!!
  --anyLarger xs x = foldl (\acc, elem => acc || greaterThan elem x) False xs
  --anyLarger xs x = (flip greaterThan .: (flip (foldl maximum))) xs x x
  --anyLarger xs =
  --  (s_comb (flip greaterThan) (((flip (foldl maximum)) . id) xs))
  --anyLarger xs x =
  --  (\x' : a, xs' : List a =>
  --    flip (
  --      flip (
  --        flip greaterThan .: (flip (foldl maximum))
  --      )
  --      x'
  --    )
  --    x' xs'
  --  )
  --  x xs
  --anyLarger xs x =
  --  (\x' : a, xs' : List a =>
  --    (greaterThan x' . (foldl maximum . id) x') xs'
  --  ) x xs

  export
  anyLargerL : Comp a => List a -> List a -> Bool
  anyLargerL Nil _ = False
  anyLargerL _ Nil = True
  anyLargerL xs@(_::_) ys@(_::_) =
    let x_max = foldl1 maximum xs
        y_min = foldl1 minimum ys in
        GT == comp x_max y_min

  export
  allLargerL : Comp a => List a -> List a -> Bool

  public export
  interface Equals a where
    eq : a -> a -> Bool

    neq : a -> a -> Bool
    neq = not .: eq

  export
  implementation Equals String where
    eq = (==)

  export
  implementation Equals Bool where
    eq True True = True
    eq False False = True
    eq _ _ = False

    neq True False = True
    neq False True = True
    neq _ _ = False

  -- f g x y = f (g x) (g y)
  x_comb : (f : a -> a -> b) -> (g : c -> a) -> (x : c) -> (y : c) -> b
  x_comb f g = (.) ((. f) (flip (.) g)) g

  export
  implementation Equals a => Equals b => Equals (a, b) where
    eq x y = eq (fst x) (fst y) && eq (snd x) (snd y)
    --eq x y = (&&) (x_comb eq fst x y) (x_comb eq snd x y)

  export
  implementation Comp a => Comp b => Comp (a, b) where
    comp x y =
      case comp (fst x) (fst y) of
           EQ => comp (snd x) (snd y)
           res => res

  export
  implementation Concat a => Concat b => Concat (a, b) where
    concat x y = (concat (fst x) (fst y), concat (snd x) (snd y))

  export
  implementation Empty a => Empty b => Empty (a, b) where
    empty = (empty, empty)

  public export
  data Tree : Type -> Type where
    Leaf : a -> Tree a
    Node : Tree a -> Tree a -> Tree a

  export
  Equals a => Equals (Tree a) where
    eq (Leaf fst) (Leaf snd) = eq fst snd
    eq (Node fl fr) (Node sl sr) = eq fl sl && eq fr sr
    eq _ _ = False

  export
  Concat (Tree a) where
    concat = Node

  export
  ShowExampleType : Type
  ShowExampleType = Maybe (Either String (List (Maybe Integer)))

  export
  showExample : ShowExampleType -> String
  showExample = show

  export
  showExampleInstance : ShowExampleType
  showExampleInstance = Just (Right ([Just 1, Just 2, Just 99, Nothing]))

namespace Interfaces.Prelude
  public export
  record UserName where
    constructor MkUserName
    name : String

  public export
  record Password where
    constructor MkPassword
    value : String

  public export
  record User where
    constructor MkUser
    name : UserName
    password : Password

  export
  hock : Interfaces.Prelude.User
  hock = MkUser (MkUserName "hock") (MkPassword "not telling")

  export
  FromString UserName where
    fromString = MkUserName

  export
  FromString Password where
    fromString = MkPassword

  export
  hock2 : Interfaces.Prelude.User
  hock2 = MkUser "hock" "not telling"

  public export
  record Complex where
    constructor MkComplex
    real : Double
    imaginary : Double

  export
  Eq Complex where
    (==) (MkComplex r1 i1) (MkComplex r2 i2) = r1 == r2 && i1 == i2

  export
  Ord Complex where
    compare (MkComplex r1 l1) (MkComplex r2 l2) =
      case compare r1 r2 of
           EQ => compare l1 l2
           res => res

  export
  Num Complex where
    (+) (MkComplex xr xi) (MkComplex yr yi) =
      MkComplex (xr + yr) (xi + yi)
    (*) (MkComplex xr xi) (MkComplex yr yi) =
      MkComplex (xr * yr - xi * yi) (xr * yi + xi * yr)
    fromInteger x = MkComplex (fromInteger x) 0

  export
  Neg Complex where
    negate (MkComplex r i) = MkComplex (negate r) (negate i)
    (-) (MkComplex xr xi) (MkComplex yr yi) =
      MkComplex (xr - yr) (xi - yi)

  export
  Fractional Complex where
    (/) (MkComplex xr xi) (MkComplex yr yi) =
      MkComplex
        ((xr * yr + xi * yi) / (yr * yr + yi * yi))
        ((xi * yr - xr * yi) / (yr * yr + yi * yi))

  export
  Show Complex where
    showPrec d (MkComplex xr xi) = showCon d "MkComplex" (showArg xr ++ showArg xi)

  public export
  record First a where
    constructor MkFirst
    value : Maybe a

  export
  Semigroup (First a) where
    (<+>) x@(MkFirst (Just _)) _ = x
    (<+>) _ y = y

  export
  Monoid (First a) where
    neutral = MkFirst Nothing

  private
  pureFirst : a -> First a
  pureFirst = MkFirst . Just

  private
  mapFirst : (a -> b) -> First a -> First b
  mapFirst f = MkFirst . map f . value

  private
  mapFirst2 : (a -> b -> c) -> First a -> First b -> First c
  mapFirst2 f (MkFirst (Just x)) = mapFirst (f x)
  mapFirst2 _ _ = neutral

  export
  Functor First where
    map = mapFirst

  export
  Applicative First where
    pure = pureFirst
    (<*>) (MkFirst (Just f)) = map f
    (<*>) _ = neutral

  export
  Monad First where
    (>>=) (MkFirst (Just x)) f = f x
    (>>=) _ _ = neutral

  export
  Eq a => Eq (First a) where
    (==) = (==) `on` value

  export
  Ord a => Ord (First a) where
    compare = compare `on` value

  export
  Show a => Show (First a) where
    show = show . value

  export
  FromString a => FromString (First a) where
    fromString = pureFirst . fromString

  export
  FromChar a => FromChar (First a) where
    fromChar = pureFirst . fromChar

  export
  FromDouble a => FromDouble (First a) where
    fromDouble = pureFirst . fromDouble

  export
  Num a => Num (First a) where
    (+) = mapFirst2 (+)
    (*) = mapFirst2 (*)
    fromInteger = pureFirst . fromInteger

  export
  Neg a => Neg (First a) where
    negate = mapFirst negate
    (-) = mapFirst2 (-)

  export
  Integral a => Integral (First a) where
    div = mapFirst2 div
    mod = mapFirst2 mod

  export
  Fractional a => Fractional (First a) where
    (/) = mapFirst2 (/)

  public export
  record Last a where
    constructor MkLast
    value : Maybe a

  export
  Semigroup (Last a) where
    (<+>) _ y@(MkLast (Just _)) = y
    (<+>) x _ = x

  export
  Monoid (Last a) where
    neutral = MkLast Nothing

  private
  pureLast : a -> Last a
  pureLast = MkLast . Just

  private
  mapLast : (a -> b) -> Last a -> Last b
  mapLast f = MkLast . map f . value

  private
  mapLast2 : (a -> b -> c) -> Last a -> Last b -> Last c
  mapLast2 f (MkLast (Just x)) = mapLast (f x)
  mapLast2 _ _ = neutral

  export
  Functor Last where
    map = mapLast

  export
  Applicative Last where
    pure = pureLast
    (<*>) (MkLast (Just f)) = map f
    (<*>) _ = neutral

  export
  Monad Last where
    (>>=) (MkLast (Just x)) f = f x
    (>>=) _ _ = neutral

  export
  Eq a => Eq (Last a) where
    (==) = (==) `on` value

  export
  Ord a => Ord (Last a) where
    compare = compare `on` value

  export
  Show a => Show (Last a) where
    show = show . value

  export
  FromString a => FromString (Last a) where
    fromString = pureLast . fromString

  export
  FromChar a => FromChar (Last a) where
    fromChar = pureLast . fromChar

  export
  FromDouble a => FromDouble (Last a) where
    fromDouble = pureLast . fromDouble

  export
  Num a => Num (Last a) where
    (+) = mapLast2 (+)
    (*) = mapLast2 (*)
    fromInteger = pureLast . fromInteger

  export
  Neg a => Neg (Last a) where
    negate = mapLast negate
    (-) = mapLast2 (-)

  export
  Integral a => Integral (Last a) where
    div = mapLast2 div
    mod = mapLast2 mod

  export
  Fractional a => Fractional (Last a) where
    (/) = mapLast2 (/)

  export
  last : List a -> Maybe a
  last = value . foldMap pureLast

  public export
  record Any where
    constructor MkAny
    any : Bool

  public export
  record All where
    constructor MkAll
    all : Bool

  export
  Semigroup Any where
    (<+>) (MkAny x) (MkAny y) = MkAny (x || y)

  export
  Monoid Any where
    neutral = MkAny False

  export
  Semigroup All where
    (<+>) (MkAll x) (MkAll y) = MkAll (x && y)

  export
  Monoid All where
    neutral = MkAll True

  export
  anyElem : (a -> Bool) -> List a -> Bool
  anyElem = any .: foldMap . (MkAny .)

  export
  allElems : (a -> Bool) -> List a -> Bool
  allElems = all .: foldMap . (MkAll .)

  public export
  record Sum a where
    constructor MkSum
    value : a

  public export
  record Product a where
    constructor MkProduct
    value : a

  export
  Num a => Semigroup (Sum a) where
    (<+>) (MkSum x) (MkSum y) = MkSum (x + y)

  export
  Num a => Monoid (Sum a) where
    neutral = MkSum 0

  export
  Num a => Semigroup (Product a) where
    (<+>) (MkProduct x) (MkProduct y) = MkProduct (x * y)

  export
  Num a => Monoid (Product a) where
    neutral = MkProduct 1

  export
  sumList : Num a => List a -> a
  sumList = value . foldMap MkSum

  export
  productList : Num a => List a -> a
  productList = value . foldMap MkProduct

  export
  FoldMapTestType : Type -> Type
  FoldMapTestType t = (First t, Last t, Sum t, Product t)

  export
  foldMapTest : Num a => List a -> FoldMapTestType a
  foldMapTest = foldMap (\x => (pureFirst x, pureLast x, MkSum x, MkProduct x))

  export
  ||| (MkFirst (Just 3), (MkLast (Just 12), (MkSum 26, MkProduct 1008)))
  foldMapTest1 : Num a => FoldMapTestType a
  foldMapTest1 = foldMapTest [3, 7, 4, 12]

  --public export
  --data ChemicalElement = H
  --                     | C
  --                     | N
  --                     | O
  --                     | F

  --export
  --atomicMass : {c : ChemicalElement} -> Double
  --atomicMass {c=H} = 1.008
  --atomicMass {c=C} = 12.011
  --atomicMass {c=N} = 14.007
  --atomicMass {c=O} = 15.999
  --atomicMass {c=F} = 18.9984

  public export
  record Mass where
    constructor MkMass
    value : Double

  export
  Eq Mass where
    (==) = (==) `on` value

  export
  Ord Mass where
    compare = compare `on` value

  export
  Show Mass where
    show = show . value

  export
  FromDouble Mass where
    fromDouble = MkMass

  export
  Semigroup Mass where
    (<+>) = MkMass .: (+) `on` value

  export
  Monoid Mass where
    neutral = 0.0

  export
  atomicMass : ChemicalElement -> Mass
  atomicMass H = 1.008
  atomicMass C = 12.011
  atomicMass N = 14.007
  atomicMass O = 15.999
  atomicMass F = 18.9984

  export
  formulaMass : List (ChemicalElement, Nat) -> Mass
  formulaMass = foldMap pairMass
    where pairMass : (ChemicalElement, Nat) -> Mass
          --pairMass = MkMass . phi (*) (value . atomicMass . fst) (cast . snd)
          pairMass = (MkMass .) $ (phi (*)) (value . atomicMass . fst) $ cast . snd

namespace Functions2
  export
  square : Double -> Double
  square = phi (*) id id

  public export
  record Stats where
    constructor MkStats
    mean      : Double
    variance  : Double
    deviation : Double

  export
  stats : List Double -> Stats
  stats xs =
    let len       := cast (length xs)
        mean      := sum xs / len
        variance  := sum (map (\x => square (x - mean)) xs) / len
        deviation := sqrt variance
     in MkStats mean variance deviation

Accounts : Type
Accounts = Vect 3 (Vect 3 Integer)

accounts : Accounts
accounts = [[1,2,3],[5,5,5],[3,1,4]]

maximum : Foldable t => t Integer -> Integer
maximum = foldr max 0

wealth : Accounts -> Integer
wealth = maximum . map sum

--maximumWealth : List (List Nat)
--maximumWealth = maximum . map sum

ls : List Integer
ls = [1,2,3,4,-1,-2,-3,-4,-5]

maxCount : List Integer -> Nat
maxCount xs = max (count (<0) xs) (count (>0) xs)

maxCount' : List Integer -> Nat
maxCount' xs = let pos = count (>0) xs
                   neg = count (<0) xs in
                   max pos neg

maximumCount : List Integer -> Nat
maximumCount xs = let pos = filter (>0) xs
                      neg = filter (<0) xs in
                      on max length pos neg

maximumCount' : List Integer -> Nat
maximumCount' xs = ((. filter (<0)) . (. filter (>0)) (on max length)) xs xs

export
infix 6 .<

(.<) : Integer -> Integer
(.<) k = if 0 < k then 1 else 0

export
infix 6 .>

(.>) : Integer -> Integer
(.>) k = if 0 > k then 1 else 0

sum' : (Integer -> Integer) -> List Integer -> Integer
sum' f xs = sum (map f xs)

MaximumCount : List Integer -> Integer
MaximumCount xs = (. sum' (.>)) ((.) max (sum' (.<)) xs) xs
--MaximumCount xs = (. sum' (.>)) (((.) max (sum' (.<))) xs) xs
--MaximumCount = map (.>)
--MaximumCount = singleton . sum . map (.>)

mc_test : Integer
mc_test = MaximumCount ls

mf : (b -> Bool) -> (a -> b) -> List a -> List b
--mf criteria = ((.) (filter criteria)) . map
--mf criteria = flip (.) map ((.) (filter criteria))
--mf criteria = (. map) ((.) (filter criteria))
mf = (. map) . (.) . filter

kestrel : a -> b -> a
kestrel a b = a

cardinal : (a -> b -> c) -> b -> a -> c
cardinal f = \b, a => f a b

cake : a -> b -> b
cake = cardinal kestrel

kite : a -> b -> b
kite = kestrel id

partial
maybeCrash : Bool -> IO String
maybeCrash False = pure "Nope!"
maybeCrash True = idris_crash "Oops!"

partial
mainCrash : Bool -> IO ()
mainCrash shouldCrash = do
  res <- maybeCrash shouldCrash
  printLn res
  printLn "Done"

pp : Functor f =>
     (f a -> f b -> f c) -> f a -> f (b -> c)
pp f = ?rhs

s_comb : (x : a -> b -> c) -> (y : a -> b) -> (z : a) -> c
s_comb x y z = x z (y z)

maximumDifference : Vect _ Integer -> Integer
maximumDifference xs = foldl max (-1)
                     $ snd
                     $ (filter (/=0)) ((s_comb (zipWith (-)) (scanl1 min)) xs)

--maximumDifference : Vect a Integer -> Integer
--maximumDifference = foldl max (-1)
--                  . filter (/=0)
--                  . (zipWith (-) <*> scanl1 min)

(++) : (n : Nat) -> (m : Nat) -> Nat
(++) n Z = n
(++) Z m = m
(++) (S n) (S m) = S (S (n ++ m))

Num Bool where
  (+) b1 b2 = case (b1, b2) of
                   (False, False) => False
                   _ => True
  (*) b1 b2 = case (b1, b2) of
                   (True, True) => True
                   _ => False
  fromInteger k = k > 0

aggregate' : (f : a -> Double) -> (xs : List a) -> Double
aggregate' = sum .: map

sqr' : Double -> Double
sqr' = flip pow 2

sqrt' : Double -> Double
sqrt' = flip pow 0.5

abs' : Double -> Double
abs' = sqrt' . sqr'

distance' : (Double -> Double) -> (Double -> Double) -> List Double -> Double
distance' = (.: aggregate')

euclidean' : List Double -> Double
euclidean' = distance' sqrt' sqr'

manhattan' : List Double -> Double
manhattan' = distance' id abs'

--distance' = (. aggregate') . (.) --!!! blackbird with g = aggregate' :DDD
--euclidean' = sqrt' . aggregate' sqr'
--manhattan' = id . aggregate' abs'
