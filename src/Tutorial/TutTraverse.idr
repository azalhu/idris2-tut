module Tutorial.TutTraverse

import Control.Applicative.Const
import Control.Monad.Identity
import Data.HList
import Data.IORef
import Data.List1
import Data.String
import Data.Validated
import Data.Vect
import Text.CSV

%default total

hreadTable1 :  (0 ts : List Type)
            -> CSVLine (HList ts)
            => List String
            -> Validated CSVError (List $ HList ts)
hreadTable1 _  Nil       = pure Nil
hreadTable1 ts (s :: ss) = [| hdecode ts 0 s :: hreadTable1 ts ss |]

traverseValidatedList :  (a -> Validated CSVError b)
                      -> List a
                      -> Validated CSVError (List b)
traverseValidatedList _ Nil       = pure Nil
traverseValidatedList f (x :: xs) = [| f x :: traverseValidatedList f xs |]

hreadTable2 :  (0 ts : List Type)
            -> CSVLine (HList ts)
            => List String
            -> Validated CSVError (List $ HList ts)
hreadTable2 ts = traverseValidatedList (hdecode ts 0)

traverseList : Applicative f => (a -> f b) -> List a -> f (List b)
traverseList _ Nil       = pure Nil
traverseList f (x :: xs) = [| f x :: traverseList f xs |]

hreadTable3 :  (0 ts : List Type)
            -> CSVLine (HList ts)
            => List String
            -> Validated CSVError (List $ HList ts)
hreadTable3 ts = traverseList (hdecode ts 0)

hreadTable4 :  (0 ts : List Type)
            -> CSVLine (HList ts)
            => List (Nat, String)
            -> Validated CSVError (List $ HList ts)
hreadTable4 ts = traverseList (uncurry $ hdecode ts)

traverseVect' : Applicative f => (a -> f b) -> Vect n a -> f (List b)
traverseVect' f = traverseList f . toList

traverseVect : Applicative f => (a -> f b) -> Vect n a -> f (Vect n b)
traverseVect _   Nil     = pure Nil
traverseVect f (x :: xs) = [| f x :: traverseVect f xs |]

sequenceList : Applicative f => List (f a) -> f (List a)
sequenceList = traverseList id

interface
Functor t => Foldable t => Traversable' t where
  traverse' : Applicative f => (a -> f b) -> t a -> f (t b)

map' : Traversable t => (a -> b) -> t a -> t b
map' f = runIdentity . traverse (Id . f)

foldMap' : Traversable t => Monoid m => (a -> m) -> t a -> m
foldMap' f = runConst . traverse (MkConst {b = ()} . f)

Traversable' List where
  traverse' _ Nil       = pure Nil
  traverse' f (x :: xs) = [|f x :: traverse' f xs |]

Traversable' List1 where
  traverse' f (x ::: xs) = [| f x ::: traverse' f xs|]

Traversable' (Either e) where
  traverse' _ (Left e)  = pure $ Left e
  traverse' f (Right a) = Right <$> f a

Traversable' Maybe where
  traverse' _ Nothing  = pure Nothing
  traverse' f (Just a) = Just <$> f a

namespace List01
  public export
  data List01 : (nonEmpty : Bool) -> Type -> Type where
    Nil  : List01 False a
    (::) : a -> List01 False a -> List01 ne a

Functor (List01 ne) where
  map _ Nil       = Nil
  map f (x :: xs) = f x :: map f xs

Foldable (List01 ne) where
  foldr _   st Nil       = st
  foldr acc st (x :: xs) = acc x $ foldr acc st xs

  foldl _   st Nil       = st
  foldl acc st (x :: xs) = foldl acc (acc st x) xs

  null Nil      = True
  null (_ :: _) = False

  foldlM _   st Nil       = pure st
  foldlM acc st (x :: xs) = acc st x >>= \st' => foldlM acc st' xs

  toList Nil       = Nil
  toList (x :: xs) = x :: toList xs

  foldMap _ Nil       = neutral
  foldMap f (x :: xs) = f x <+> foldMap f xs

Traversable (List01 ne) where
  traverse _ Nil       = pure Nil
  traverse f (x :: xs) = [| f x :: traverse f xs |]

record Tree a where
  constructor Node
  tValue  : a
  forest : List (Tree a)

Forest : Type -> Type
Forest = List . Tree

treeMap : (a -> b) -> Tree a -> Tree b
treeMap g (Node v f) = Node (g v) $ go f
  where go : Forest a -> Forest b
        go Nil       = Nil
        go (x :: xs) = treeMap g x :: go xs

treeFoldr : (a -> s -> s) -> s -> Tree a -> s
treeFoldr acc st (Node v f) = acc v $ go st f
  where go : s -> Forest a -> s
        go st Nil       = st
        go st (x :: xs) = treeFoldr acc (go st xs) x

treeFoldl : (s -> a -> s) -> s -> Tree a -> s
treeFoldl acc st (Node v f) = go (acc st v) f
  where go : s -> Forest a -> s
        go st Nil       = st
        go st (x :: xs) = go (treeFoldl acc st x)  xs

treeNull : Tree a -> Bool
treeNull = const False

treeFoldlM : Monad m => (s -> a -> m s) -> s -> Tree a -> m s
treeFoldlM acc st (Node v f) = go (acc st v) f
  where go : m s -> Forest a -> m s
        go st Nil       = st
        go st (x :: xs) = st >>= \st' => go (treeFoldlM acc st' x) xs

treeToList : Tree a -> List a
treeToList (Node v f) = go [<v] f
  where go : SnocList a -> Forest a -> List a
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) = go (sx <>< treeToList x) xs

treeFoldMap : Monoid m => (a -> m) -> Tree a -> m
treeFoldMap g (Node v f) = go (g v) f
  where go : m -> Forest a -> m
        go acc Nil       = acc
        go acc (x :: xs) = go (acc <+> treeFoldMap g x) xs

treeTraverse : Applicative m => (a -> m b) -> Tree a -> m (Tree b)
treeTraverse g (Node v f) = [| Node (g v) $ go f |]
  where go : Forest a -> m (Forest b)
        go Nil       = pure Nil
        go (x :: xs) = [| treeTraverse g x :: go xs |]

Functor Tree where
  map = treeMap

Foldable Tree where
  foldr   = treeFoldr
  foldl   = treeFoldl
  null    = treeNull
  foldlM  = treeFoldlM
  toList  = treeToList
  foldMap = treeFoldMap

Traversable Tree where
  traverse = treeTraverse

treeTest : Tree Integer
treeTest = Node 0 [Node 1 [Node 2 [Node 3 [], Node 4 []], Node 5 [Node 6 []]], Node 7 []]

data Crud : (i, a : Type) -> Type where
  Create : (value : a) -> Crud i a
  Update : (id : i) -> (value : a) -> Crud i a
  Read   : (id : i) -> Crud i a
  Delete : (id : i) -> Crud i a

Functor (Crud i) where
  map f (Create va)    = Create $ f va
  map f (Update vi va) = Update vi $ f va
  map f (Read vi)      = Read vi
  map f (Delete vi)    = Delete vi

Foldable (Crud i) where
  foldr acc st (Create va)    = acc va st
  foldr acc st (Update vi va) = acc va st
  foldr acc st (Read vi)      = st
  foldr acc st (Delete vi)    = st

  foldl acc st (Create va)    = acc st va
  foldl acc st (Update vi va) = acc st va
  foldl acc st (Read vi)      = st
  foldl acc st (Delete vi)    = st

  null (Create va)    = False
  null (Update vi va) = False
  null (Read vi)      = True
  null (Delete vi)    = True

  foldlM acc st (Create va)    = acc st va
  foldlM acc st (Update vi va) = acc st va
  foldlM acc st (Read vi)      = pure st
  foldlM acc st (Delete vi)    = pure st

  toList (Create va)    = [va]
  toList (Update vi va) = [va]
  toList (Read vi)      = []
  toList (Delete vi)    = []

  foldMap f (Create va)    = f va
  foldMap f (Update vi va) = f va
  foldMap f (Read vi)      = neutral
  foldMap f (Delete vi)    = neutral

Traversable (Crud i) where
  traverse f (Create va)    = Create <$> f va
  traverse f (Update vi va) = Update vi <$> f va
  traverse f (Read vi)      = pure $ Read vi
  traverse f (Delete vi)    = pure $ Delete vi

data Response : (e, i, a : Type) -> Type where
  Created : (id : i) -> (value : a) -> Response e i a
  Updated : (id : i) -> (value : a) -> Response e i a
  Found   : (values : List a) -> Response e i a
  Deleted : (id : i) -> Response e i a
  Error   : (err : e) -> Response e i a

Functor (Response e i) where
  map f (Created vi va) = Created vi $ f va
  map f (Updated vi va) = Updated vi $ f va
  map f (Found vas)     = Found $ map f vas
  map f (Deleted vi)    = Deleted vi
  map f (Error ve)      = Error ve

Foldable (Response e i) where
  foldr acc st (Created vi va) = acc va st
  foldr acc st (Updated vi va) = acc va st
  foldr acc st (Found vas)     = foldr acc st vas
  foldr acc st (Deleted vi)    = st
  foldr acc st (Error ve)      = st

  foldl acc st (Created vi va) = acc st va
  foldl acc st (Updated vi va) = acc st va
  foldl acc st (Found vas)     = foldl acc st vas
  foldl acc st (Deleted vi)    = st
  foldl acc st (Error ve)      = st

  null (Created vi va) = False
  null (Updated vi va) = False
  null (Found vas)     = null vas
  null (Deleted vi)    = True
  null (Error ve)      = True

  foldlM acc st (Created vi va) = acc st va
  foldlM acc st (Updated vi va) = acc st va
  foldlM acc st (Found vas)     = foldlM acc st vas
  foldlM acc st (Deleted vi)    = pure st
  foldlM acc st (Error ve)      = pure st

  toList (Created vi va) = [va]
  toList (Updated vi va) = [va]
  toList (Found vas)     = vas
  toList (Deleted vi)    = []
  toList (Error ve)      = []

  foldMap f (Created vi va) = f va
  foldMap f (Updated vi va) = f va
  foldMap f (Found vas)     = foldMap f vas
  foldMap f (Deleted vi)    = neutral
  foldMap f (Error ve)      = neutral

Traversable (Response e i) where
  traverse f (Created vi va) = Created vi <$> f va
  traverse f (Updated vi va) = Updated vi <$> f va
  traverse f (Found vas)     = Found <$> traverse f vas
  traverse f (Deleted vi)    = pure $ Deleted vi
  traverse f (Error ve)      = pure $ Error ve

record Comp (f, g : Type -> Type) (a : Type) where
  constructor MkComp
  unComp : f $ g a

Functor f => Functor g => Functor (Comp f g) where
  map fun = MkComp . (map . map) fun . unComp

Foldable f => Foldable g => Foldable (Comp f g) where
  foldr acc st = (foldr . flip . foldr) acc st . unComp

  foldl acc st = (foldl . foldl) acc st . unComp

  null = null . unComp

  foldlM acc st = (foldlM . foldlM) acc st . unComp

  toList = foldMap toList . toList . unComp

  foldMap fun = (foldMap . foldMap) fun . unComp

Traversable f => Traversable g => Traversable (Comp f g) where
  traverse fun = map MkComp . (traverse . traverse) fun . unComp

record Product (f, g : Type -> Type) (a : Type) where
  constructor MkProduct
  fst : f a
  snd : g a

Functor f => Functor g => Functor (Product f g) where
  map fun (MkProduct vf vs) = MkProduct (map fun vf) (map fun vs)

zipWithIndex : List a -> List (Nat,a)
zipWithIndex = go 1 Lin
  where go : Nat -> SnocList (Nat,a) -> List a -> List (Nat,a)
        go _ sx Nil       = sx <>> Nil
        go n sx (x :: xs) = go (S n) (sx :< (n,x)) xs

pairWithIndexIO : IORef Nat -> a -> IO (Nat,a)
pairWithIndexIO ref va = do
  ix <- readIORef ref
  writeIORef ref (S ix)
  pure (ix,va)

zipListWithIndexIO : IORef Nat -> List a -> IO (List (Nat,a))
zipListWithIndexIO ref = traverse $ pairWithIndexIO ref

zipWithIndexIO : Traversable t => IORef Nat -> t a -> IO (t (Nat,a))
zipWithIndexIO = traverse . pairWithIndexIO

zipFromZeroIO : Traversable t => t a -> IO (t (Nat,a))
zipFromZeroIO ta = newIORef Z >>= (`zipWithIndexIO` ta)

Stateful : (st : Type) -> (a : Type) -> Type
Stateful st a = st -> (st,a)

pairWithIndex' : a -> Stateful Nat (Nat,a)
pairWithIndex' v index = (S index, (index,v))

record State st a where
  constructor ST
  runST : st -> (st,a)

pairWithIndex : a -> State Nat (Nat,a)
pairWithIndex v = ST $ \index => (S index, (index,v))

namespace State
  public export
  get : State st st
  get = ST $ \s => (s,s)
  
  public export
  put : st -> State st ()
  put v = ST $ \_ => (v,())
  
  public export
  modify : (st -> st) -> State st ()
  modify f = ST $ \v => (f v,())
  
  public export
  runState : st -> State st a -> (st,a)
  runState = flip runST
  
  public export
  evalState : st -> State st a -> a
  evalState = snd .: runState
  
  public export
  execState : st -> State st a -> st
  execState = fst .: runState

Functor (State st) where
  map f (ST run) = ST $ \s =>
    let (s2,va) := run s
     in (s2, f va)

Applicative (State st) where
  (ST fun) <*> (ST val) = ST $ \s =>
    let (s2,f)  := fun s
        (s3,va) := val s2
     in (s3, f va)
  pure v = ST $ \s => (s,v)

Monad (State st) where
  (ST val) >>= f = ST $ \s =>
    let (s2,va) := val s
     in runST (f va) s2

rnd : Bits64 -> Bits64
rnd seed = fromInteger
         $ (437799614237992725 * cast seed) `mod` 2305843009213693951

Gen : Type -> Type
Gen = State Bits64

bits64 : Gen Bits64
bits64 = get <* modify rnd
--bits64 = ST $ \s => (rnd s, s)

range64 : (upper : Bits64) -> Gen Bits64
range64 18446744073709551615 = bits64
range64 n                    = (`mod` (n + 1)) <$> bits64
--  s <- bits64
--  pure $ s `mod` upper + 1

interval64 : (a,b : Bits64) -> Gen Bits64
interval64 a b =
  let mi := min a b
      ma := max a b
   in (mi +) <$> range64 (ma - mi)
--  s <- range64 a
--  pure $ s - a + b

interval : Num n => Cast n Bits64 => (a,b : n) -> Gen n
interval a b = fromInteger . cast <$> interval64 (cast a) (cast b)

bool : Gen Bool
bool = (== 0) <$> range64 1

fin : {n : _} -> Gen (Fin $ S n)
fin = fromMaybe FZ . (`natToFin` (S n)) <$> interval 0 n
--fin = fromInteger . cast <$> interval 0 n

element : {n : _} -> Vect (S n) a -> Gen a
element xs = (`index` xs) <$> fin

vect : {n : _} -> Gen a -> Gen (Vect n a)
vect = sequence . replicate n
--vect {n = Z}   _ = pure Nil
--vect {n = S k} v = [| v :: vect v |]

list : Gen Nat -> Gen a -> Gen (List a)
list gnat ga = gnat >>= \n => toList <$> vect {n} ga
--list n v = n >>= \k => go k v
--  where go : Nat -> Gen a -> Gen (List a)
--        go Z     _ = pure Nil
--        go (S k) v = [| v :: go k v |]

testGen : Bits64 -> Gen a -> Vect 10 a
testGen = (. vect) . evalState

choice : {n : _} -> Vect (S n) (Gen a) -> Gen a
choice = join . element

either : Gen a -> Gen b -> Gen (Either a b)
either ga gb = choice [Left <$> ga, Right <$> gb]
--either ga gb = do
--  rb <- bool
--  if rb
--     then Right <$> gb
--     else Left <$> ga

printableAscii : Gen Char
printableAscii = chr <$> interval 32 126

string : Gen Nat -> Gen Char -> Gen String
string = map pack .: list

data HListF : (f : Type -> Type) -> (ts : List Type) -> Type where
  Nil  : HListF f Nil
  (::) : (x : f t) -> (xs : HListF f ts) -> HListF f (t :: ts)

hlist' : HListF Gen ts -> Gen (HList ts)
hlist' Nil       = pure Nil
hlist' (x :: xs) = [| x :: hlist' xs |]

hlist : Applicative f => HListF f ts -> f (HList ts)
hlist Nil       = pure Nil
hlist (x :: xs) = [| x :: hlist xs |]

uncons : Vect (S n) a -> (Vect n a, a)
uncons (x :: xs) = (xs, x)

record IxState s t a where
  constructor IxST
  runIxST : s -> (t,a)

Functor (IxState s t) where
  map f (IxST run) = IxST $ \vs =>
    let (vt,va) := run vs
     in (vt, f va)

Applicative (IxState s s) where
  pure va = IxST $ \vs => (vs,va)
  IxST ff <*> IxST fa= IxST $ \vr =>
    let (vs,f)  := ff vr
        (vt,va) := fa vs
     in (vt, f va)

Monad (IxState s s) where
  IxST fa >>= f = IxST $ \vr =>
    let (vs,va) := fa vr
     in runIxST (f va) vs

namespace ApplicativeIxState
  public export
  pure : a -> IxState s s a
  pure va = IxST $ \vs => (vs,va)

  public export
  (<*>) : IxState r s (a -> b) -> IxState s t a -> IxState r t b
  IxST ff <*> IxST fa = IxST $ \vr =>
    let (vs,f)  := ff vr
        (vt,va) := fa vs
     in (vt, f va)

  public export
  (>>=) : IxState r s a -> (a -> IxState s t b) -> IxState r t b
  IxST fa >>= f = IxST $ \vr =>
    let (vs,va) := fa vr
     in runIxST (f va) vs

  public export
  (>>) : IxState r s () -> Lazy (IxState s t b) -> IxState r t b
  IxST fu >> IxST fb = IxST $ \vr =>
    let (vs,()) := fu vr
     in fb vs

  public export
  join : IxState r s (IxState s t a) -> IxState r t a
  join = (>>= id)

interface
Functor (m s t) => IxApplicative (0 m : Type -> Type -> Type -> Type)  where
  pure  : a -> m s s a
  (<*>) : m r s (a -> b) -> m s t a -> m r t b

interface
IxApplicative m => IxMonad m where
  (>>=) : m r s a -> (a -> m s t b) -> m r t b
  (>>)  : m r s () -> Lazy (m s t b) -> m r t b
  join : m r s (m s t a) -> m r t a


IxApplicative IxState where
  pure va = IxST $ \vs => (vs,va)

  IxST ff <*> IxST fa = IxST $ \vr =>
    let (vs,f)  := ff vr
        (vt,va) := fa vs
     in (vt, f va)

IxMonad IxState where
  IxST fa >>= f = IxST $ \vr =>
    let (vs,va) := fa vr
     in runIxST (f va) vs

  IxST fu >> IxST fb = IxST $ \vr =>
    let (vs,()) := fu vr
     in fb vs

  join = (>>= id)

get : IxState s s s
get = IxST $ \vs => (vs,vs)

put : t -> IxState s t ()
put vt = IxST $ \_ => (vt,())

modify : (s -> t) -> IxState s t ()
modify f = IxST $ \vs => (f vs,())

runState : s -> IxState s t a -> (t,a)
runState = flip runIxST

evalState : s -> IxState s t a -> a
evalState = snd .: runState

execState : s -> IxState s t a -> t
execState = fst .: runState

tagAndDecode :  (0 ts : List Type)
             -> CSVLine (HList ts)
             => String
             -> State Nat (Validated CSVError (HList ts))
tagAndDecode ts s = uncurry (hdecode ts) <$> pairWithIndex s

readTable :  (0 ts : List Type)
          -> CSVLine (HList ts)
          => List String
          -> Validated CSVError (List $ HList ts)
readTable ts = evalState 1 . traverse @{%search} @{Compose} (tagAndDecode ts)

traverseComp :  Traversable t
             => Applicative f
             => Applicative g
             => (a -> f (g b))
             -> t a
             -> f (g (t b))
traverseComp = traverse @{%search} @{Compose}

readTable' :  (0 ts : List Type)
           -> CSVLine (HList ts)
           => List String
           -> Validated CSVError (List $ HList ts)
readTable' ts = evalState 1 . traverseComp (tagAndDecode ts)

data Line : Type -> Type where
  Annotated : String -> a -> Line a
  Clean     : a -> Line a

Functor Line where
  map f (Annotated s l) = Annotated s $ f l
  map f (Clean l)       = Clean $ f l

Foldable Line where
  foldr acc st (Annotated s l) = acc l st
  foldr acc st (Clean l)       = acc l st

  foldl acc st (Annotated s l) = acc st l
  foldl acc st (Clean l)       = acc st l

  null = const False

  foldlM acc st (Annotated s l) = acc st l
  foldlM acc st (Clean l)       = acc st l

  toList (Annotated s l) = [l]
  toList (Clean l)       = [l]

  foldMap f (Annotated s l) = f l
  foldMap f (Clean l)       = f l

Traversable Line where
  traverse f (Annotated s l) = Annotated s <$> f l
  traverse f (Clean l)       = Clean <$> f l

readLine : String -> Line String
readLine s = case split ('#' ==) s of
  h ::: [t] => Annotated t h
  _         => Clean s

readCSV :  (0 ts : List Type)
        -> CSVLine (HList ts)
        => String
        -> Validated CSVError (List $ Line $ HList ts)
readCSV ts = evalState 1
           . traverse @{Compose} @{Compose} (tagAndDecode ts)
           . map readLine
           . lines

validInput : String
validInput = """
  f,12,-13.01#this is a comment
  t,100,0.0017
  t,1,100.8#color: red
  f,255,0.0
  f,24,1.12e17
  """

invalidInput : String
invalidInput = """
  o,12,-13.01#another comment
  t,100,0.0017
  t,1,abc
  f,256,0.0
  f,24,1.12e17
  """

data Tagged : (tag, value : Type) -> Type where
  Tag  : tag -> value -> Tagged tag value
  Pure : value -> Tagged tag value

Functor (Tagged tag) where
  map f (Tag t v) = Tag t $ f v
  map f (Pure v)  = Pure $ f v

Foldable (Tagged tag) where
  foldr acc st (Tag t v) = acc v st
  foldr acc st (Pure v)  = acc v st

  foldl acc st (Tag t v) = acc st v
  foldl acc st (Pure v)  = acc st v

  null = const False

  foldlM acc st (Tag t v) = acc st v
  foldlM acc st (Pure v)  = acc st v

  toList (Tag t v) = [v]
  toList (Pure v)  = [v]

  foldMap f (Tag t v) = f v
  foldMap f (Pure v)  = f v

Traversable (Tagged tag) where
  traverse f (Tag t v) = Tag t <$> f v
  traverse f (Pure v)  = Pure <$> f v

Bifunctor Tagged where
  bimap f g (Tag t v) = Tag (f t) (g v)
  bimap f g (Pure v)  = Pure $ g v

  mapFst f (Tag t v) = Tag (f t) v
  mapFst f (Pure v)  = Pure v

  mapSnd g (Tag t v) = Tag t (g v)
  mapSnd g (Pure v)  = Pure (g v)

Bifoldable Tagged where
  bifoldr f g st (Tag t v) = f t $ g v st
  bifoldr f g st (Pure v)  = g v st

  bifoldl f g st (Tag t v) = g (f st t) v
  bifoldl f g st (Pure v)  = g st v

  binull = const False

Bitraversable Tagged where
  bitraverse f g (Tag t v) = Tag <$> (f t) <*> (g v)
  bitraverse f g (Pure v)  = Pure <$> g v

record Biff (p : Type -> Type -> Type) (f,g : Type -> Type) (a,b : Type) where
  constructor MkBiff
  runBiff : p (f a) (g b)

Bifunctor p => Functor f => Functor g => Bifunctor (Biff p f g) where
  bimap ff fg = MkBiff . bimap (map ff) (map fg) . runBiff
  mapFst ff = MkBiff . bimap (map ff) (map id) . runBiff
  mapSnd fg = MkBiff . bimap (map id) (map fg) . runBiff

Bifoldable p => Foldable f => Foldable g => Bifoldable (Biff p f g) where
  bifoldr ff fg st = bifoldr (flip $ foldr ff) (flip $ foldr fg) st . runBiff
  bifoldl ff fg st = bifoldl (foldl ff) (foldl fg) st . runBiff
  binull = binull . runBiff

Bitraversable p => Traversable f => Traversable g =>
  Bitraversable (Biff p f g) where
    bitraverse ff fg =
      map MkBiff . bitraverse (traverse ff) (traverse fg) . runBiff

record Tannen (f : Type -> Type) (p : Type -> Type -> Type) (a,b : Type) where
  constructor MkTannen
  runTannen : f (p a b)

Functor f => Bifunctor p => Bifunctor (Tannen f p) where
  bimap fa fb = MkTannen . map (bimap fa fb) . runTannen
  mapFst fa = MkTannen . map (bimap fa id) . runTannen
  mapSnd fb = MkTannen . map (bimap id fb) . runTannen

Foldable f => Bifoldable p => Bifoldable (Tannen f p) where
  bifoldr fa fb st = foldr (flip $ bifoldr fa fb) st . runTannen
  bifoldl fa fb st = foldl (bifoldl fa fb) st . runTannen
  binull = null . runTannen

Traversable f => Bitraversable p => Bitraversable (Tannen f p) where
  bitraverse fa fb = map MkTannen . traverse (bitraverse fa fb) . runTannen

data TagError : Type where
  CE         : CSVError -> TagError
  InvalidTag : (line : Nat) -> (tag : String) -> TagError
  Append     : TagError -> TagError -> TagError

Semigroup TagError where (<+>) = Append

data Color = Red | Green | Blue

readColor : String -> State Nat (Validated TagError Color)
readColor s = flip decodeTag s <$> get
  where decodeTag : Nat -> String -> Validated TagError Color
        decodeTag k "red"   = pure Red
        decodeTag k "green" = pure Green
        decodeTag k "blue"  = pure Blue
        decodeTag k s       = Invalid $ InvalidTag k s

--readColor s = uncurry decodeTag . (`MkPair` s) <$> get
--  where decodeTag : Nat -> String -> Validated TagError Color
--readColor c = ST $ \vs => MkPair vs $ case trim c of
--                                           "red"   => Valid Red
--                                           "green" => Valid Green
--                                           "blue"  => Valid Blue
--                                           _       => Invalid $ InvalidTag vs c

readTaggedLine : String -> Tagged String String
readTaggedLine s = case split ('#' ==) s of
  h ::: [t] => Tag t h
  _         => Pure s

tagAndDecodeTE :  (0 ts : List Type)
               -> CSVLine (HList ts)
               => String
               -> State Nat (Validated TagError (HList ts))
tagAndDecodeTE ts s = mapFst CE . uncurry (hdecode ts) <$> pairWithIndex s

readTagged :  (0 ts : List Type)
           -> CSVLine (HList ts)
           => String
           -> Validated TagError (List $ Tagged Color $ HList ts)
readTagged ts = map runTannen
              . evalState 1
              . bitraverse @{%search} @{Compose} readColor (tagAndDecodeTE ts)
              . MkTannen {f = List} {p = Tagged}
              . map readTaggedLine
              . lines

--tagAndDecode :  (0 ts : List Type)
--             -> CSVLine (HList ts)
--             => String
--             -> State Nat (Validated CSVError (HList ts))
--tagAndDecode ts s = uncurry (hdecode ts) <$> pairWithIndex s

--readCSV :  (0 ts : List Type)
--        -> CSVLine (HList ts)
--        => String
--        -> Validated CSVError (List $ Line $ HList ts)
--readCSV ts = evalState 1
--           . traverse @{Compose} @{Compose} (tagAndDecode ts)
--           . map readLine
--           . lines

