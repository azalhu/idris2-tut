module Tutorial.TutFunctor

import Data.IORef
import Data.List1
import Data.String
import Data.Vect

%default total

phi : (a : p -> q -> r) ->
      (b : y -> p) ->
      (c : y -> q) ->
      (x : y) -> r
phi a b c x = a (b x) (c x)

interface
Functor' (0 f : Type -> Type) where
  map' : (a -> b) -> f a -> f b

interface
Functor' f => Applicative' f where
  app   : f (a -> b) -> f a -> f b
  pure' : a -> f a

multBy2List : Num a => List a -> List a
multBy2List []        = []
multBy2List (x :: xs) = 2 * x :: multBy2List xs

toUpperList : List String -> List String
toUpperList []        = []
toUpperList (x :: xs) = toUpper x :: toUpperList xs

toLengthList : List String -> List Nat
toLengthList []        = []
toLengthList (x :: xs) = length x :: toLengthList xs

mapList : (a -> b) -> List a -> List b
mapList f []        = []
mapList f (x :: xs) = f x :: mapList f xs

multBy2List' : Num a => List a -> List a
multBy2List' = mapList (2 *)

toUpperList' : List String -> List String
toUpperList' = mapList toUpper

toLengthList' : List String -> List Nat
toLengthList' = mapList length

mapMaybe : (a -> b) -> Maybe a -> Maybe b
mapMaybe f Nothing  = Nothing
mapMaybe f (Just v) = Just $ f v

mapIO : (a -> b) -> IO a -> IO b
mapIO f io = fromPrim $ mapPrimIO (toPrim io)
  where mapPrimIO : PrimIO a -> PrimIO b
        mapPrimIO prim w =
          let MkIORes va w2 = prim w
           in MkIORes (f va) w2

mapConstIO : b -> IO a -> IO b
mapConstIO = mapIO . const

forgetIO : IO a -> IO ()
forgetIO = mapConstIO ()

public export
data List01 : (nonEmpty : Bool) -> Type -> Type where
  Nil  : List01 False a
  (::) : a -> List01 False a -> List01 ne a

implementation
Functor (List01 ne) where
  map _ Nil       = Nil
  map f (x :: xs) = f x :: map f xs

implementation
Functor' Maybe where
  map' _ Nothing  = Nothing
  map' f (Just v) = Just $ f v

implementation
Functor' List where
  map' _ Nil       = Nil
  map' f (x :: xs) = f x :: map' f xs

implementation
Functor' List1 where
  map' f (x ::: xs) = f x ::: map' f xs

implementation
Functor' (Vect n) where
  map' _ Nil       = Nil
  map' f (x :: xs) = f x :: map' f xs

implementation
Functor' (Either e) where
  map' _ (Left ve)  = Left ve
  map' f (Right va) = Right $ f va

implementation
Functor' (Pair a) where
  map' f (MkPair x y) = MkPair x (f y)

implementation
Functor' (List01 ne) where
  map' _ Nil       = Nil
  map' f (x :: xs) = f x :: map' f xs

tailShowReversNoOp : Show a => List1 a -> List String
tailShowReversNoOp xs = map (reverse . show) (tail xs)

tailShowReverse : Show a => List1 a -> List String
tailShowReverse xs = reverse . show <$> tail xs

public export
record Product (f, g : Type -> Type) (a : Type) where
  constructor MkProduct
  fst : f a
  snd : g a

implementation
Functor f => Functor g => Functor (Product f g) where
  map f (MkProduct l r) = MkProduct (map f l) (map f r)

implementation
Applicative f => Applicative g => Applicative (Product f g) where
  pure = phi MkProduct pure pure
  MkProduct ffl ffr <*> MkProduct fal far =
    MkProduct (ffl <*> fal) (ffr <*> far)

toPair : Product f g a -> (f a, g a)
toPair (MkProduct fst snd) = (fst, snd)

fromPair : (f a, g a) -> Product f g a
fromPair (fst, snd) = MkProduct fst snd

productExample :  Show a
               => (Either e a, List a)
               -> (Either e String, List String)
productExample = toPair . map show . fromPair {f = Either e, g = List}

public export
record Comp (f, g : Type -> Type) (a : Type) where
  constructor MkComp
  unComp  : f . g $ a

implementation
Functor f => Functor g => Functor (Comp f g) where
  map f (MkComp v) = MkComp $ map f <$> v

implementation
Applicative f => Applicative g => Applicative (Comp f g) where
  pure = MkComp . pure . pure
  MkComp ff <*> MkComp fa = MkComp [| ff <*> fa |]

compExample :  Show a => List (Either e a) -> List (Either e String)
compExample = unComp . map show . MkComp {f = List, g = Either e}

compTest : List (Either Integer String)
compTest = compExample [Left 3, Right 5]

record Comp' (f, g, h : Type -> Type) (a : Type) where
  constructor MkComp'
  unComp'  : f . g . h $ a

implementation
Functor f => Functor g => Functor h => Functor (Comp' f g h) where
  map f (MkComp' v) = MkComp' $ ((f <$>) <$>) <$> v

compExample' :  Show a => List (Either e (Maybe a)) -> List (Either e (Maybe String))
compExample' = unComp' . map show . MkComp' {f = List, g = Either e, h = Maybe}

compTest' : List (Either (Maybe Integer) (Maybe String))
compTest' = compExample' [Left (Just 3), Left Nothing, Right (Just 5), Right Nothing]

[Compose'] Functor f => Functor g => Functor (f . g) where
  map = map . map

compExample2 :  Show a => List (Either e a) -> List (Either e String)
compExample2 = map @{Compose'} show

compTest2 : List (Either Integer String)
compTest2 = compExample2 [Left 3, Right 5]

[Compose''] Functor f => Functor g => Functor h => Functor (f . g . h) where
  map = map . map . map

compExample2' :  Show a => List (Either e (Maybe a)) -> List (Either e (Maybe String))
compExample2' = map @{Compose''} show

compTest2' : List (Either (Maybe Integer) (Maybe String))
compTest2' = compExample2' [Left (Just 3), Left Nothing, Right (Just 5), Right Nothing]

[Product'] Functor f => Functor g => Functor (\a => (f a, g a)) where
  map h (f, g) = (map h f, map h g)

record Identity a where
  constructor Id
  value : a

implementation
Functor Identity where
  map f (Id v) = Id $ f v

record Const (e, a : Type) where
  constructor MkConst
  value : e

implementation
Functor (Const e) where
  map _ (MkConst v) = MkConst v

data Crud : (i : Type) -> (a : Type) -> Type where
  Create : (value : a) -> Crud i a
  Update : (id : i) -> (value : a) -> Crud i a
  Read   : (id : i) -> Crud i a
  Delete : (id : i) -> Crud i a

implementation
Functor (Crud i) where
  map f (Create value)    = Create (f value)
  map f (Update id value) = Update id (f value)
  map _ (Read id)         = Read id
  map _ (Delete id)       = Delete id

data Response : (e, i, a : Type) -> Type where
  Created : (id : i) -> (value : a) -> Response e i a
  Updated : (id : i) -> (value : a) -> Response e i a
  Found   : (values : List a) -> Response e i a
  Deleted : (id : i) -> Response e i a
  Error   : (err : e) -> Response e i a

implementation
Functor (Response e i) where
  map f (Created id value) = Created id $ f value
  map f (Updated id value) = Updated id $ f value
  map f (Found values)     = Found $ map f values
  map _ (Deleted id)       = Deleted id
  map _ (Error err)        = Error err

data Validated : (e, a : Type) -> Type where
  Invalid : (err : e) -> Validated e a
  Valid   : (val : a) -> Validated e a

implementation
Functor (Validated e) where
  map _ (Invalid err) = Invalid err
  map f (Valid val)   = Valid $ f val

implementation
Semigroup e => Applicative (Validated e) where
  pure = Valid
  Valid f    <*> Valid v    = Valid $ f v
  Valid _    <*> Invalid e  = Invalid e
  Invalid e1 <*> Invalid e2 = Invalid $ e1 <+> e2
  Invalid e  <*> Valid _    = Invalid e

implementation
Semigroup e => Monad (Validated e) where
  Valid   v >>= f = f v
  Invalid e >>= _ = Invalid e

liftMaybe2 : (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
liftMaybe2 f (Just va) (Just vb) = Just (f va vb)
liftMaybe2 _ _         _         = Nothing

liftVect2 : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
liftVect2 f (va :: vas) (vb :: vbs) = f va vb :: liftVect2 f vas vbs
liftVect2 _ Nil         Nil         = Nil

liftIO2 : (a -> b -> c) -> IO a -> IO b -> IO c
liftIO2 f ioa iob = do
  va <- ioa
  vb <- iob
  pure $ f va vb

liftIO2' : (a -> b -> c) -> IO a -> IO b -> IO c
liftIO2' f ioa iob = fromPrim $ go (toPrim ioa) (toPrim iob)
  where go : PrimIO a -> PrimIO b -> PrimIO c
        go pa pb w =
          let MkIORes va w2 = pa w
              MkIORes vb w3 = pb w2
           in MkIORes (f va vb) w3

multNumbers : Num a => Neg a => IO (Maybe a)
multNumbers = do
  s1 <- getLine
  s2 <- getLine
  pure $ liftMaybe2 (*) (parseInteger s1) (parseInteger s2)

liftMaybe3 : (a -> b -> c -> d) -> Maybe a -> Maybe b -> Maybe c -> Maybe d
liftMaybe3 f (Just va) (Just vb) (Just vc) = Just $ f va vb vc
liftMaybe3 _ _         _         _         = Nothing

pureMaybe : a -> Maybe a
pureMaybe = Just

multAdd100 : Num a => Neg a => String -> String -> Maybe a
multAdd100 s t = liftMaybe3 calc (parseInteger s) (parseInteger t) (pure 100)
  where calc : a -> a -> a -> a
        calc x y z = x * y + z

implementation
Applicative' Maybe where
  app (Just fun) (Just val) = Just $ fun val
  app _          _          = Nothing

  pure' = Just

liftA'2 : Applicative' f => (a -> b -> c) -> f a -> f b -> f c
liftA'2 fun fa fb = (pure' fun `app` fa) `app` fb

liftA'3 : Applicative' f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA'3 fun fa fb fc = ((pure' fun `app` fa) `app` fb) `app` fc

liftA'2' : Applicative' f => (a -> b -> c) -> f a -> f b -> f c
liftA'2' fun fa fb = (fun `map'` fa) `app` fb

liftA'3' : Applicative' f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA'3' fun fa fb fc = ((fun `map'` fa) `app` fb) `app` fc

liftA2 : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 fun fa fb = pure fun <*> fa <*> fb

liftA3 : Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 fun fa fb fc = pure fun <*> fa <*> fb <*> fc

liftA2' : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2' fun fa fb = fun <$> fa <*> fb

liftA3' : Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3' fun fa fb fc = fun <$> fa <*> fb <*> fc

||| `liftA2` using the syntactic sugar of `idiom brackets`
liftA2'' : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2'' fun fa fb = [| fun fa fb |]

||| `liftA3` using the syntactic sugar of `idiom brackets`
liftA3'' : Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3'' fun fa fb fc = [| fun fa fb fc |]

data Gender = Male | Female | Other

record Name where
  constructor MkName
  value : String

record Email where
  constructor MkEmail
  value : String

record Password where
  constructor MkPassword
  value : String

record User where
  constructor MkUser
  firstName : Name
  lastName  : Name
  age       : Maybe Nat
  email     : Email
  gender    : Gender
  password  : Password

data CSVError : Type where
  FieldError           : (line, column : Nat) -> (str : String) -> CSVError
  UnexpectedEndOfInput : (line, column : Nat) -> CSVError
  ExpectedEndOfInput   : (line, column : Nat) -> CSVError
  App                  : (fst, snd : CSVError)  -> CSVError

Semigroup CSVError where
  (<+>) = App

interface CSVField a where
  read : String -> Maybe a

interface CSVLine a where
  decodeAt : (line, col : Nat) -> List String -> Validated CSVError a

CSVField Gender where
  read "m" = Just Male
  read "f" = Just Female
  read "o" = Just Other
  read _   = Nothing

CSVField Bool where
  read "t" = Just True
  read "f" = Just False
  read _   = Nothing

CSVField Nat where
  read = parsePositive

CSVField Integer where
  read = parseInteger

CSVField Double where
  read = parseDouble

CSVField a => CSVField (Maybe a) where
  read "" = Just Nothing
  read s  = Just <$> read s

readIf : (String -> Bool) -> (String -> a) -> String -> Maybe a
readIf p mk s = if p s then Just (mk s) else Nothing

isValidName : String -> Bool
isValidName s =
  let len = length s
   in 0 < len && len <= 100 && all isAlpha (unpack s)

CSVField Name where
  read = readIf isValidName MkName

isEmailChar : Char -> Bool
isEmailChar '.' = True
isEmailChar '@' = True
isEmailChar c = isAlphaNum c

isValidEmail : String -> Bool
isValidEmail s =
  let len = length s
   in 0 < len && len <= 100 && all isEmailChar (unpack s)

CSVField Email where
  read = readIf isValidEmail MkEmail

isPasswordChar : Char -> Bool
isPasswordChar ' ' = True
--- isSpace holds as well for other characters than ' '
--- e.g. non-breaking space '\160'
--- only ' ' is allowed in passwords
isPasswordChar c   = not (isControl c) && not (isSpace c)

isValidPassword : String -> Bool
isValidPassword s =
  let len = length s
   in 8 < len && len <= 100 && all isPasswordChar (unpack s)

CSVField Password where
  read = readIf isValidPassword MkPassword

readField : CSVField a => (line, column : Nat) -> String -> Validated CSVError a
readField line col str =
  maybe (Invalid $ FieldError line col str) Valid (read str)

toVect : (n : Nat) -> (line, col : Nat) -> List a -> Validated CSVError (Vect n a)
toVect Z     _    _   Nil       = Valid Nil
toVect Z     line col _         = Invalid $ ExpectedEndOfInput line col
toVect (S k) line col Nil       = Invalid $ UnexpectedEndOfInput line col
toVect (S k) line col (x :: xs) = (x ::) <$> toVect k line (S col) xs

readUser' : (line : Nat) -> List String -> Validated CSVError User
readUser' line ss = do
  [fn,ln,a,em,g,pw] <-  toVect 6 line 0 ss
  [| MkUser (readField line 1 fn)
            (readField line 2 ln)
            (readField line 3 a)
            (readField line 4 em)
            (readField line 5 g)
            (readField line 6 pw) |]

readUser : (line : Nat) -> String -> Validated CSVError User
readUser line = readUser' line . forget . split (',' ==)

namespace HList
  public export
  data HList : (ts : List Type) -> Type where
    Nil  : HList Nil
    (::) : (v : t) -> (vs : HList ts) -> HList (t :: ts)

  export
  head : HList (t :: _) -> t
  head (v :: _) = v

  export
  tail : HList (_ :: ts) -> HList ts
  tail (_ :: vs) = vs

  export
  (++) : HList as -> HList bs -> HList (as ++ bs)
  (++) Nil       ys = ys
  (++) (x :: xs) ys = x :: xs ++ ys

  export
  indexList : (as : List a) -> Fin (length as) -> a
  indexList (v :: _)  FZ     = v
  indexList (_ :: vs) (FS k) = indexList vs k

  export
  index : (ix : Fin (length ts)) -> HList ts -> indexList ts ix
  index FZ (v :: _)      = v
  index (FS k) (_ :: vs) = index k vs

  export
  hlift : (a -> b) -> HList [a] -> b
  hlift f [x] = f x

  export
  hlift2 : (a -> b -> c) -> HList [a, b] -> c
  hlift2 f [x, y] = f x y

namespace HVect
  public export
  data HVect : (ts : Vect n Type) -> Type where
    Nil  : HVect Nil
    (::) : (v : t) -> (vs : HVect ts) -> HVect (t :: ts)

  export
  head : HVect (t :: _) -> t
  head (v :: _) = v

  export
  tail : HVect (_ :: ts) -> HVect ts
  tail (_ :: vs) = vs

  export
  (++) : HVect xs -> HVect ys -> HVect (xs ++ ys)
  (++) Nil       ys = ys
  (++) (x :: xs) ys = x :: xs ++ ys

  export
  index :  {0 n : Nat}
        -> {0 ts : Vect n Type}
        -> (ix : Fin n)
        -> HVect ts
        -> index ix ts
  index FZ     (v :: _)  = v
  index (FS k) (_ :: vs) = index k vs

  export
  empties : {n : Nat} -> {0 ts : Vect n Type} -> HVect (Vect 0 <$> ts)
  empties {n = Z}   {ts = Nil}    = Nil
  empties {n = S _} {ts = _ :: _} = Nil :: empties

  export
  hcons :  {0 ts : Vect n Type}
        -> HVect ts
        -> HVect (Vect m <$> ts)
        -> HVect (Vect (S m) <$> ts)
  hcons Nil       Nil       = Nil
  hcons (v :: vs) (w :: ws) = (v :: w) :: hcons vs ws

  export
  htranspose :  {n : Nat}
             -> {0 ts : Vect n Type}
             -> Vect m (HVect ts)
             -> HVect (Vect m <$> ts)
  htranspose Nil       = empties
  htranspose (v :: vs) = hcons v $ htranspose vs

  export
  vects : Vect 3 (HVect [Bool, Nat, String])
  vects = [[True, 100, "Hello"], [False, 0, "Idris"], [False, 2, "!"]]

  export
  vects' : HVect (Vect 3 <$> [Bool, Nat, String])
  vects' = [[True, False, False], [100, 0, 2], ["Hello", "Idris", "!"]]

  export
  vects_transposed : HVect (Vect 3 <$> [Bool, Nat, String])
  vects_transposed = htranspose vects

CSVLine (HList Nil) where
  decodeAt _ _ Nil = Valid Nil
  decodeAt l c _   = Invalid $ ExpectedEndOfInput l c

CSVField t => CSVLine (HList ts) => CSVLine (HList (t :: ts)) where
  decodeAt l c Nil       = Invalid $ UnexpectedEndOfInput l c
  decodeAt l c (s :: ss) = [| readField l c s :: decodeAt l (S c) ss |]

decode : CSVLine a => (line : Nat) -> String -> Validated CSVError a
decode line = decodeAt line 1 . forget . split (',' ==)

hdecode :  (0 ts : List Type)
        -> CSVLine (HList ts)
        => (line : Nat)
        -> String
        -> Validated CSVError (HList ts)
hdecode _ = decode

decodeCRUD :  CSVField i
           => CSVField a
           => (line : Nat)
           -> (s    : String)
           -> Validated CSVError (Crud i a)
decodeCRUD l s = do
  let h ::: t := split (',' ==) s
  MkName n <- readField l 1 h
  case n of
    "Create" => hlift  Create <$> decodeAt l 2 t
    "Update" => hlift2 Update <$> decodeAt l 2 t
    "Read"   => hlift  Read   <$> decodeAt l 2 t
    "Delete" => hlift  Delete <$> decodeAt l 2 t
    _        => Invalid $ FieldError l 1 n

Applicative' (Either e) where
  app (Left err)  _           = Left err
  app _           (Left err)  = Left err
  app (Right fun) (Right val) = Right $ fun val

  pure' = Right

Functor' Identity where
  map' f (Id v) = Id $ f v

Applicative' Identity where
  app (Id fun) (Id val) = Id $ fun val

  pure' = Id

{n : _} -> Applicative' (Vect n) where
  app _         Nil       = Nil
  app (f :: fs) (x :: xs) = f x :: app fs xs

  pure' = replicate n

Monoid e => Applicative' (Pair e) where
  app (e1, fa) (e2, va) = (e1 <+> e2, fa va)

  pure' va = (neutral, va)

Monoid e => Functor' (Const e) where
  map' f (MkConst v) = MkConst v

Monoid e => Applicative' (Const e) where
  app (MkConst e1) (MkConst e2) = MkConst $ e1 <+> e2

  pure' _ = MkConst neutral

Monoid e => Applicative (Const e) where
  MkConst e1 <*> MkConst e2 = MkConst $ e1 <+> e2

  pure _ = MkConst neutral

Functor' (Validated e) where
  map' _ (Invalid err) = Invalid err
  map' f (Valid val)   = Valid $ f val

Semigroup e => Applicative' (Validated e) where
  app (Invalid e1) (Invalid e2) = Invalid $ e1 <+> e2
  app (Invalid e)  _            = Invalid e
  app _            (Invalid e)  = Invalid e
  app (Valid f)    (Valid v)    = Valid $ f v

  pure' = Valid

a_map : Applicative m => (a -> b) -> m a -> m b
a_map f ma = pure f <*> ma

m_app : Monad m => m (a -> b) -> m a -> m b
m_app mf ma = mf >>= \f => ma >>= \a => pure $ f a

m_map : Monad m => (a -> b) -> m a -> m b
m_map f ma = ma >>= \a => pure $ f a

j_bind : Monad m => m a -> (a -> m b) -> m b
j_bind ma f = join $ f <$> ma

b_join : Monad m => m (m a) -> m a
b_join = (>>= id)

-- email addresses in the DB must be unique!
-- size limit of DB is 1000 entries!
-- looking up user by ID must fail with `UserNotFound` when entry not found in the DB!
DB : Type
DB = IORef (List (Nat, User))

data DBError : Type where
  UserExists        : Email -> Nat -> DBError
  UserNotFound      : Nat -> DBError
  SizeLimitExceeded : DBError

-- Abstraction of: someDBProg : arg1 -> arg2 -> DB -> IO (Either DBError a)
record Prog a where
  constructor MkProg
  runProg : DB -> IO (Either DBError a)

Eq Email where
  MkEmail s1 == MkEmail s2 = s1 == s2

Functor Prog where
  map f (MkProg run) = MkProg $ map (map f) . run

Applicative Prog where
  pure v = MkProg $ \_ => pure . Right $ v
  MkProg rf <*> MkProg ra = MkProg $ \db => do
    Right fun <- rf db | Left err => pure . Left $ err
    Right va  <- ra db | Left err => pure . Left $ err
    pure . Right $ fun va

Monad Prog where
  MkProg ra >>= f = MkProg $ \db => do
    Right va <- ra db | Left err => pure . Left $ err
    runProg (f va) db

HasIO Prog where
  liftIO act = MkProg $ \_ => Right <$> act

throw : DBError -> Prog a
throw err = MkProg $ \_ => pure . Left $ err

getUsers : Prog (List (Nat, User))
getUsers = MkProg $ map Right . readIORef

putUsers : List (Nat, User) -> Prog ()
putUsers users =
  if length users > 1000 then throw SizeLimitExceeded
  else MkProg $ \db => Right <$> writeIORef db users

modifyDB : (List (Nat, User) -> List (Nat, User)) -> Prog ()
modifyDB f = getUsers >>= putUsers . f

lookupUser : (id : Nat) -> Prog User
lookupUser id = do
  users <- getUsers
  let Just user := lookup id users 
    | Nothing => throw $ UserNotFound id
  pure user

deleteUser : (id : Nat) -> Prog ()
deleteUser id =
  ignore (lookupUser id) >> modifyDB (filter $ (id /=) . fst)

newId : List (Nat, User) -> Nat
newId = S . foldl (\n1,(n2,_) => max n1 n2) Z

findUserByEmail : Email -> List (Nat, User) -> Maybe (Nat, User)
findUserByEmail email' = find ((email' ==) . email . snd)

throwIfEmailExists : Email -> List (Nat, User) -> Prog ()
throwIfEmailExists email users = do
  let Nothing := findUserByEmail email users
    | Just (id, _) => throw $ UserExists email id
  pure ()

addUser : (new : User) -> Prog Nat
addUser new = do
  users <- getUsers
  throwIfEmailExists new.email users
  let newId := newId users
  putUsers $ (newId, new) :: users
  pure newId

updateUser : (id : Nat) -> (mod : User -> User) -> Prog User
updateUser id mod = do
  user <- lookupUser id
  let newUser := mod user
  users <- getUsers
  throwIfEmailExists newUser.email (filter ((id /=) . fst) users)
  let newUsers := replaceWhen ((id ==) . fst) (id, newUser) users
  putUsers newUsers $> newUser

update' : Eq a => a -> b -> List (a, b) -> List (a, b)
update' va vb = map (\p@(va', vb') => if va == va' then (va, vb) else p)

updateUser' : (id : Nat) -> (mod : User -> User) -> Prog User
updateUser' id mod = do
  u  <- mod <$> lookupUser id
  us <- getUsers
  case find ((u.email ==) . email . snd) us of
       Just (id', _) => if id /= id'
                           then throw $ UserExists u.email id'
                           else putUsers (update' id u us) $> u
       Nothing       => putUsers (update' id u us) $> u

record Prog' env err a where
  constructor MkProg'
  runProg' : env -> IO (Either err a)

Functor (Prog' env err) where
  map f (MkProg' run) = MkProg' $ map (map f) . run

Applicative (Prog' env err) where
  pure v = MkProg' $ \_ => pure . Right $ v
  MkProg' rf <*> MkProg' ra = MkProg' $ \db => do
    Right fun <- rf db | Left err => pure . Left $ err
    Right va  <- ra db | Left err => pure . Left $ err
    pure . Right $ fun va

Monad (Prog' env err) where
  MkProg' ra >>= f = MkProg' $ \db => do
    Right va <- ra db | Left err => pure . Left $ err
    runProg' (f va) db

HasIO (Prog' env err) where
  liftIO act = MkProg' $ \_ => Right <$> act

throw' : err -> Prog' env err a
throw' err = MkProg' $ \env => pure . Left $ err




-- ProgRT

record ProgRT err a where
  constructor MkProgRT
  execute : IO (Either err a)

Functor (ProgRT err) where
  map f (MkProgRT exec) = MkProgRT $ map (map f) exec

Applicative (ProgRT err) where
  pure v = MkProgRT $ pure . Right $ v
  MkProgRT rf <*> MkProgRT ra = MkProgRT [| rf <*> ra |]

Monad (ProgRT err) where
  MkProgRT ra >>= f = MkProgRT $ do
    Right va <- ra | Left err => pure . Left $ err
    execute $ f va

HasIO (ProgRT err) where
  liftIO act = MkProgRT $ Right <$> act

throwRT : err -> ProgRT err a
throwRT err = MkProgRT $ pure . Left $ err

-- Prog by ProgRT

record Prog'' env err a where
  constructor MkProg''
  runProg'' : env -> ProgRT err a

Functor (Prog'' env err) where
  map f (MkProg'' run) = MkProg'' $ map f . run

Applicative (Prog'' env err) where
  pure v = MkProg'' $ \_ => pure v
  MkProg'' rf <*> MkProg'' ra = MkProg'' $ \db => do
    fun <- rf db
    va  <- ra db
    pure $ fun va

Monad (Prog'' env err) where
  MkProg'' ra >>= f = MkProg'' $ \db => do
    va <- ra db
    runProg'' (f va) db

HasIO (Prog'' env err) where
  liftIO act = MkProg'' $ \_ => liftIO act

throw'' : err -> Prog'' env err a
throw'' err = MkProg'' $ \env => throwRT err





-- ProgRT

record ProgRT' err a where
  constructor MkProgRT'
  execute : IO (Either err a)

Functor (ProgRT' err) where
  map f (MkProgRT' exec) = MkProgRT' $ map (map f) exec

Applicative (ProgRT' err) where
  pure v = MkProgRT' $ pure . Right $ v
  MkProgRT' rf <*> MkProgRT' ra = MkProgRT' [| rf <*> ra |]

Monad (ProgRT' err) where
  MkProgRT' ra >>= f = MkProgRT' $ do
    Right va <- ra | Left err => pure . Left $ err
    execute $ f va

HasIO (ProgRT' err) where
  liftIO act = MkProgRT' $ Right <$> act

throwRT' : err -> ProgRT' err a
throwRT' err = MkProgRT' $ pure . Left $ err

-- Prog by ProgRT'

record Prog''' env err a where
  constructor MkProg'''
  runProg''' : env -> ProgRT' err a

Functor (Prog''' env err) where
  map f (MkProg''' run) = MkProg''' $ map f . run

Applicative (Prog''' env err) where
  pure v = MkProg''' $ \_ => pure v
  MkProg''' rf <*> MkProg''' ra = MkProg''' $ \db => do
    fun <- rf db
    va  <- ra db
    pure $ fun va

Monad (Prog''' env err) where
  MkProg''' ra >>= f = MkProg''' $ \db => do
    va <- ra db
    runProg''' (f va) db

HasIO (Prog''' env err) where
  liftIO act = MkProg''' $ \_ => liftIO act

throw''' : err -> Prog''' env err a
throw''' err = MkProg''' $ \env => throwRT' err

