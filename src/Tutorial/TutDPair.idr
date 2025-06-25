module Tutorial.TutDPair

import Control.Monad.State

import Data.DPair
import Data.Either
import Data.HVect
import Data.List
import Data.List1
import Data.Singleton
import Data.String
import Data.Vect

import Text.CSV

%default total

parseAndDrop : Vect (3 + n) String -> Maybe (Vect n Nat)
parseAndDrop = map (drop 3) . traverse parsePositive

takeWhile' : (a -> Bool) -> Vect n a -> Vect m a
takeWhile'' : forall a, n, m . (a -> Bool) -> Vect n a -> Vect m a
takeWhile''' :  {0 a : _}
             -> {0 n : _}
             -> {0 m : _}
             -> (a -> Bool)
             -> Vect n a
             -> Vect m a

voids : Vect 7 Void
voids = takeWhile' (const True) Nil

proofOfVoid : Void
proofOfVoid = head voids

record AnyVect a where
  constructor MkAnyVect
  length : Nat
  vect   : Vect length a

takeWhile : (a -> Bool) -> Vect n a -> AnyVect a
takeWhile _ Nil       = MkAnyVect _ Nil
takeWhile f (x :: xs) = case f x of
  False => MkAnyVect _ Nil
  True  => let MkAnyVect _ ys = takeWhile f xs in MkAnyVect _ (x :: ys)

takeWhileTR : (a -> Bool) -> Vect n a -> AnyVect a
takeWhileTR f = go Nil
  where go : {k : _} -> Vect k a -> Vect j a -> AnyVect a
        go sx Nil       = MkAnyVect _ sx
        go sx (x :: xs) = case f x of
          False => MkAnyVect _ sx
          True  => go (snoc sx x) xs

takeWhile3 : (a -> Bool) -> Vect m a -> (n ** Vect n a)
takeWhile3 _ Nil       = (_ ** Nil)
takeWhile3 f (x :: xs) = case f x of
  False => (_ ** Nil)
  True  => let (_ ** ys) = takeWhile3 f xs in (_ ** x :: ys)

takeWhileTR3 : (a -> Bool) -> Vect m a -> (n ** Vect n a)
takeWhileTR3 f = go Nil
  where go : {k : _} -> Vect k a -> Vect j a -> (k ** Vect k a)
        go sx Nil       = (_ ** sx)
        go sx (x :: xs) = case f x of
          False => (_ ** sx)
          True  => go (snoc sx x) xs

takeWhileExists : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
takeWhileExists _ Nil       = Evidence _ Nil
takeWhileExists f (x :: xs) = case f x of
  False => Evidence _ Nil
  True  => let Evidence _ ys = takeWhileExists f xs in Evidence _ (x :: ys)

-- notice how `k` is not an implicit argument to `go`
-- since `k` in `Exists k` is erased at compile time
takeWhileExistsTR : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
takeWhileExistsTR f = go Nil
  where go : Vect k a -> Vect j a -> Exists (\k => Vect k a)
        go sx Nil       = Evidence _ sx
        go sx (x :: xs) = case f x of
          False => Evidence _ sx
          True  => go (snoc sx x) xs

record DPair' (a : Type) (p : a -> Type) where
  constructor MkDPair'
  fst : a
  snd : p fst

AnyVect' : (a : Type) -> Type
AnyVect' a = DPair Nat (\n => Vect n a)

AnyVect'' : (a : Type) -> Type
AnyVect'' a = (n : Nat ** Vect n a)

AnyVect3 : (a : Type) -> Type
AnyVect3 a = (n ** Vect n a)

AnyMatrix : (a : Type) -> Type
AnyMatrix a = (m ** n ** Vect m $ Vect n a)

true : Singleton True
true = Val True

true' : Singleton True
true' = Val _

vectLength : Vect n a -> Singleton n
vectLength Nil       = Val _
vectLength (_ :: xs) = let Val _ = vectLength xs in Val _

bogusLength : Vect n a -> Nat
bogusLength _ = Z

toDPair : Exists (\n => Vect n a) -> (m ** Vect m a)
toDPair (Evidence _ as) = let Val _ := vectLength as in (_ ** as)

filterVect : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
filterVect _ Nil       = Evidence _ Nil
filterVect p (x :: xs) =
  let Evidence _ ys := filterVect p xs
   in case p x of
        False => Evidence _ ys
        True  => Evidence _ $ x :: ys

filterVectTR : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
filterVectTR p = go Nil
  where go : Vect k a -> Vect j a -> Exists (\k => Vect k a)
        go sx Nil       = Evidence _ sx
        go sx (x :: xs) = case p x of
          False => go sx xs
          True  => go (snoc sx x) xs

mapMaybeVect : (a -> Maybe b) -> Vect m a -> Exists (\n => Vect n b)
mapMaybeVect _ Nil       = Evidence _ Nil
mapMaybeVect f (x :: xs) =
  let Evidence _ ys := mapMaybeVect f xs
   in case f x of
        Nothing => Evidence _ ys
        Just y  => Evidence _ $ y :: ys

mapMaybeVectTR : (a -> Maybe b) -> Vect m a -> Exists (\n => Vect n b)
mapMaybeVectTR f = go Nil
  where go : Vect k b -> Vect j a -> Exists (\k => Vect k b)
        go sx Nil       = Evidence _ sx
        go sx (x :: xs) = case f x of
          Nothing => go sx xs
          Just y  => go (snoc sx y) xs

dropWhileVect : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
dropWhileVect _ Nil       = Evidence _ Nil
dropWhileVect p (x :: xs) = case p x of
  False => Evidence _ (x :: xs)
  True  => dropWhileVect p xs

dropWhileVect' : (a -> Bool) -> Vect m a -> (n ** Vect n a)
dropWhileVect' = toDPair .: dropWhileVect

data BaseType = DNABase | RNABase

Show BaseType where
  show DNABase = "DNABase"
  show RNABase = "RNABase"

data Nucleobase : BaseType -> Type where
  Adenine  : Nucleobase b
  Cytosine : Nucleobase b
  Guanine  : Nucleobase b
  Thymine  : Nucleobase DNABase
  Uracile  : Nucleobase RNABase

Show (Nucleobase b) where
  show Adenine  = "Adenine"
  show Cytosine = "Cytosine"
  show Guanine  = "Guanine"
  show Thymine  = "Thymine"
  show Uracile  = "Uracile"

NucleicAcid : BaseType -> Type
NucleicAcid = List . Nucleobase

RNA : Type
RNA = NucleicAcid RNABase

DNA : Type
DNA = NucleicAcid DNABase

encodeBase : Nucleobase b -> Char
encodeBase Adenine  = 'A'
encodeBase Cytosine = 'C'
encodeBase Guanine  = 'G'
encodeBase Thymine  = 'T'
encodeBase Uracile  = 'U'

encode : NucleicAcid b -> String
encode = pack . map encodeBase

failing "Mismatch between: RNABase and DNABase."
  errDNA : DNA
  errDNA = [Uracile, Adenine]

dna1 : DNA
dna1 = [Adenine, Cytosine, Guanine]

rna1 : RNA
rna1 = [Adenine, Cytosine, Guanine]

readAnyBase : Char -> Maybe (Nucleobase b)
readAnyBase 'A' = Just Adenine
readAnyBase 'C' = Just Cytosine
readAnyBase 'G' = Just Guanine
readAnyBase _   = Nothing

readRNABase : Char -> Maybe (Nucleobase RNABase)
readRNABase 'U' = Just Uracile
readRNABase c   = readAnyBase c

readDNABase : Char -> Maybe (Nucleobase DNABase)
readDNABase 'T' = Just Thymine
readDNABase c   = readAnyBase c

readRNA : String -> Maybe RNA
readRNA = traverse readRNABase . unpack

readDNA : String -> Maybe DNA
readDNA = traverse readDNABase . unpack

complementRNA' : RNA -> RNA
complementRNA' = map calc
  where calc : Nucleobase RNABase -> Nucleobase RNABase
        calc Guanine  = Cytosine
        calc Cytosine = Guanine
        calc Adenine  = Uracile
        calc Uracile  = Adenine

complementDNA' : DNA -> DNA
complementDNA' = map calc
  where calc : Nucleobase DNABase -> Nucleobase DNABase
        calc Guanine  = Cytosine
        calc Cytosine = Guanine
        calc Adenine  = Thymine
        calc Thymine  = Adenine

complementBase'' : Nucleobase b -> Nucleobase b
complementBase'' Adenine  = ?what_now
complementBase'' Cytosine = Guanine
complementBase'' Guanine  = Cytosine
complementBase'' Thymine  = Adenine
complementBase'' Uracile  = Adenine

complementBase : {b : _} -> Nucleobase b -> Nucleobase b
complementBase {b = DNABase} Adenine  = Thymine
complementBase {b = RNABase} Adenine  = Uracile
complementBase               Cytosine = Guanine
complementBase               Guanine  = Cytosine
complementBase               Thymine  = Adenine
complementBase               Uracile  = Adenine

complementBaseTwice :  {b : _}
                    -> (nb : Nucleobase b)
                    -> complementBase {b} (complementBase {b} nb) = nb
complementBaseTwice {b = DNABase} Adenine  = Refl
complementBaseTwice {b = RNABase} Adenine  = Refl
complementBaseTwice {b = DNABase} Cytosine = Refl
complementBaseTwice {b = RNABase} Cytosine = Refl
complementBaseTwice {b = DNABase} Guanine  = Refl
complementBaseTwice {b = RNABase} Guanine  = Refl
complementBaseTwice {b = DNABase} Thymine  = Refl
complementBaseTwice {b = RNABase} Uracile  = Refl

const' : (a : _) -> b -> Singleton a
const' x = const (Val x)

complement : {b : _} -> NucleicAcid b -> NucleicAcid b
complement = map complementBase

complementTwice : {b : _} -> (na : NucleicAcid b) -> complement (complement na) = na
complementTwice Nil       = Refl
complementTwice (x :: xs) = cong2 (::) (complementBaseTwice x) (complementTwice xs)

data Result : Type where
  UnknownBaseType : String -> Result
  InvalidSequence : String -> Result
  GotDNA          : DNA -> Result
  GotRNA          : RNA -> Result

data RNAOrDNA = ItsRNA RNA | ItsDNA DNA

namespace InputError
  public export
  data InputError : Type where
    UnknownBaseType : String -> InputError
    InvalidSequence : String -> InputError

  public export
  Show InputError where
    show (UnknownBaseType str) = "Unknown base type: \{str}"
    show (InvalidSequence str) = "Invalid sequence: \{str}"

readAcid : (b : BaseType) -> String -> Either InputError (NucleicAcid b)
readAcid b str =
  let err = InvalidSequence str
   in case b of
        DNABase => maybeToEither err $ readDNA str
        RNABase => maybeToEither err $ readRNA str

getNucleicAcid : IO (Either InputError (b ** NucleicAcid b))
getNucleicAcid = do
  baseString <- getLine
  case baseString of
    "DNA" => map (MkDPair _) . readAcid DNABase <$> getLine
    "RNA" => map (MkDPair _) . readAcid RNABase <$> getLine
    _     => pure $ Left $ UnknownBaseType baseString

transcribeBase : Nucleobase DNABase -> Nucleobase RNABase
transcribeBase Adenine  = Uracile
transcribeBase Cytosine = Guanine
transcribeBase Guanine  = Cytosine
transcribeBase Thymine  = Adenine

transcribe : DNA -> RNA
transcribe = map transcribeBase

printRNA : RNA -> IO ()
printRNA = putStrLn . encode

transcribeProg : IO ()
transcribeProg = do
  Right (b ** seq) <- getNucleicAcid
    | Left err => putStrLn $ show err
  case b of
    DNABase => printRNA $ transcribe seq
    RNABase => printRNA seq

Acid1 : Type
Acid1 = (b ** NucleicAcid b)

record Acid2 where
  constructor MkAcid2
  baseType : BaseType
  sequence : NucleicAcid baseType

data Acid3 : Type where
  SomeRNA : RNA -> Acid3
  SomeDNA : DNA -> Acid3

from1To2 : Acid1 -> Acid2
from1To2 (b ** seq) = MkAcid2 b seq

from2To1 : Acid2 -> Acid1
from2To1 $ MkAcid2 b seq = (b ** seq)

from1To3 : Acid1 -> Acid3
from1To3 (RNABase ** seq) = SomeRNA seq
from1To3 (DNABase ** seq) = SomeDNA seq

from3To1 : Acid3 -> Acid1
from3To1 $ SomeRNA seq = (_ ** seq)
from3To1 $ SomeDNA seq = (_ ** seq)

from2To3 : Acid2 -> Acid3
from2To3 = from1To3 . from2To1

from3To2 : Acid3 -> Acid2
from3To2 = from1To2 . from3To1

data Dir = Sense | Antisense

data Nucleobase' : BaseType -> Dir -> Type where
  Adenine'  : Nucleobase' b d
  Cytosine' : Nucleobase' b d
  Guanine'  : Nucleobase' b d
  Thymine'  : Nucleobase' DNABase d
  Uracile'  : Nucleobase' RNABase d

NucleicAcid' : BaseType -> Dir -> Type
NucleicAcid' = List .: Nucleobase'

RNA' : Dir -> Type
RNA' = NucleicAcid' RNABase

DNA' : Dir -> Type
DNA' = NucleicAcid' DNABase

inverse : Dir -> Dir
inverse Sense     = Antisense
inverse Antisense = Sense

complementBase' : {b : _} -> Nucleobase' b d -> Nucleobase' b (inverse d)
complementBase' {b = DNABase} Adenine'  = Thymine'
complementBase' {b = RNABase} Adenine'  = Uracile'
complementBase'               Cytosine' = Guanine'
complementBase'               Guanine'  = Cytosine'
complementBase'               Thymine'  = Adenine'
complementBase'               Uracile'  = Adenine'

complement' : {b : _} -> NucleicAcid' b d -> NucleicAcid' b (inverse d)
complement' = map complementBase'

transcribeBase' : Nucleobase' DNABase Antisense -> Nucleobase' RNABase Sense
transcribeBase' Adenine'  = Uracile'
transcribeBase' Cytosine' = Guanine'
transcribeBase' Guanine'  = Cytosine'
transcribeBase' Thymine'  = Adenine'

transcribe' : DNA' Antisense -> RNA' Sense
transcribe' = map transcribeBase'

transcribeAny : {d : _} -> DNA' d -> RNA' Sense
transcribeAny {d = Antisense} = transcribe'
transcribeAny {d = Sense}     = transcribe' . complement'

record DAcid where
  constructor MkDAcid
  baseType : BaseType
  dir      : Dir
  sequence : NucleicAcid' baseType dir

readAnyBase' : {auto d : _} -> Char -> Maybe (Nucleobase' b d)
readAnyBase' 'A' = Just Adenine'
readAnyBase' 'C' = Just Cytosine'
readAnyBase' 'G' = Just Guanine'
readAnyBase' _   = Nothing

readRNABase' : {auto d : _} -> Char -> Maybe (Nucleobase' RNABase d)
readRNABase' 'U' = Just Uracile'
readRNABase' c   = readAnyBase' c

readDNABase' : {auto d : _} -> Char -> Maybe (Nucleobase' DNABase d)
readDNABase' 'T' = Just Thymine'
readDNABase' c   = readAnyBase' c

readDir : String -> Maybe (d : Dir ** String)
readDir str = case forget $ split ('-' ==) str of
  ["5´", str, "3´"] => Just (Sense ** str)
  ["3´", str, "5´"] => Just (Antisense ** str)
  _                 => Nothing

readRNA' : String -> Maybe DAcid
readRNA' str = do
  (d ** seq) <- readDir str
  rna <- traverse readRNABase' $ unpack seq
  Just $ MkDAcid RNABase d rna

readDNA' : String -> Maybe DAcid
readDNA' str = do
  (d ** seq) <- readDir str
  dna <- traverse readDNABase' $ unpack seq
  Just $ MkDAcid DNABase d dna

encodeDir : Dir -> String -> String
encodeDir Sense     = (`joinBy` ["5´-", "-3´"])
encodeDir Antisense = (`joinBy` ["3´-", "-5´"])

encodeBase' : Nucleobase' b d -> Char
encodeBase' Adenine'  = 'A'
encodeBase' Cytosine' = 'C'
encodeBase' Guanine'  = 'G'
encodeBase' Thymine'  = 'T'
encodeBase' Uracile'  = 'U'

encode' : {d : _} -> NucleicAcid' b d -> String
encode' = encodeDir d . pack . map encodeBase'

readAcid' : (b : BaseType) -> String -> Either InputError DAcid
readAcid' b str =
  let err = InvalidSequence str
   in case b of
        DNABase => maybeToEither err $ readDNA' str
        RNABase => maybeToEither err $ readRNA' str

getNucleicAcid' : IO (Either InputError DAcid)
getNucleicAcid' = do
  baseString <- getLine
  case baseString of
    "DNA" => readAcid' DNABase <$> getLine
    "RNA" => readAcid' RNABase <$> getLine
    _     => pure $ Left $ UnknownBaseType baseString

printRNA' : {d : _} -> RNA' d -> IO ()
printRNA' {d = Sense}     = putStrLn . encode'
printRNA' {d = Antisense} = putStrLn . encode' . complement'

transcribeProg' : IO ()
transcribeProg' = do
  Right (MkDAcid baseType _ sequence) <- getNucleicAcid'
    | Left err => putStrLn $ show err
  case baseType of
    DNABase => printRNA' $ transcribeAny sequence
    RNABase => printRNA' sequence

data ColType0 : (complete : Bool) -> Type where
  I64      : ColType0 b
  Str      : ColType0 b
  Boolean  : ColType0 b
  Float    : ColType0 b
  BigInt   : ColType0 b
  Natural  : ColType0 b
  Finite   : Nat -> ColType0 b
  Optional : ColType0 False -> ColType0 True

ColType : Type
ColType = ColType0 True

record Schema where
  constructor MkSchema
  len  : Nat
  cols : Vect len ColType

IdrisType : ColType0 b -> Type
IdrisType $ I64        = Int64
IdrisType $ Str        = String
IdrisType $ Boolean    = Bool
IdrisType $ Float      = Double
IdrisType $ BigInt     = Integer
IdrisType $ Natural    = Nat
IdrisType $ Finite n   = Fin n
IdrisType $ Optional t = Maybe $ IdrisType t

Row : Schema -> Type
Row schema = HVect schema.len $ map IdrisType schema.cols

indexRow : {ts : _} -> (ix : Fin ts.len) -> Row ts -> IdrisType (index ix ts.cols)
indexRow {ts = MkSchema (S k) cs} ix vs = ?lhs2
indexRow {ts = MkSchema Z _}      _  _  impossible

record Table where
  constructor MkTable
  schema : Schema
  size   : Nat
  rows   : Vect size (Row schema)

QueryPair : Schema -> Type
QueryPair schema = (ix : Fin schema.len ** IdrisType (index ix schema.cols))

data Command : (t : Table) -> Type where
  Clear       : Command t
  PrintSchema : Command t
  PrintSize   : Command t
  PrintTable  : Command t
  New         : (newSchema : Schema) -> Command t
  Prepend     : Row t.schema -> Command t
  Get         : Fin t.size -> Command t
  Query       : QueryPair t.schema -> Command t
  Delete      : Fin t.size -> Command t
  Quit        : Command t

applyCommand : (t : Table) -> Command t -> Table
applyCommand t                 Clear       = MkTable t.schema _ Nil
applyCommand t                 PrintSchema = t
applyCommand t                 PrintSize   = t
applyCommand t                 PrintTable  = t
applyCommand _                 (New ts)    = MkTable ts _ Nil
applyCommand (MkTable ts n rs) (Prepend r) = MkTable ts _ $ r :: rs
applyCommand t                 (Get x)     = t
applyCommand t                 (Query c)   = t
applyCommand t                 Quit        = t
applyCommand (MkTable ts n rs) (Delete x)  = case n of
  S k => MkTable ts k $ deleteAt x rs
  Z   => absurd x

data OOBType = OOBTable | OOBColumn

data Error : Type where
  UnknownCommand : String -> Error
  UnknownType    : (pos : Nat) -> String -> Error
  InvalidField   : (pos : Nat) -> ColType0 b -> String -> Error
  ExpectedEOI    : (pos : Nat) -> String -> Error
  UnexpectedEOI  : (pos : Nat) -> String -> Error
  OutOfBounds    : (tp : OOBType) -> (size : Nat) -> (index : Nat) -> Error
  NoNat          : String -> Error

showOOBTypeErrMsg : OOBType -> String
showOOBTypeErrMsg OOBTable  = "Size of table"
showOOBTypeErrMsg OOBColumn = "Length of row"

showColType : ColType0 b -> String
showColType $ I64        = "i64"
showColType $ Str        = "str"
showColType $ Boolean    = "boolean"
showColType $ Float      = "float"
showColType $ BigInt     = "bigint"
showColType $ Natural    = "natural"
showColType $ Finite n   = "fin\{show n}"
showColType $ Optional t = "\{showColType t}?"

showSchema : Schema -> String
showSchema schema = concat $ intersperse "," $ map showColType schema.cols

allTypes : String
allTypes = joinBy ", "
         . map (showColType {b = True})
         $ [I64,Str,Boolean,Float]

showError : Error -> String
showError (UnknownCommand x) = """
  Unknown command: \{x}.
  Known commands are: clear, schema, size, new, add, get, query, delete, quit.
  """

showError (UnknownType pos x) = """
  Unknown type at position \{show pos}: \{x}.
  Known types are: \{allTypes}.
  """

showError (InvalidField pos tpe x) = """
  Invalid value at position \{show pos}.
  Expected type: \{showColType tpe}.
  Value found: \{x}.
  """

showError (ExpectedEOI k x) = """
  Expected end of input.
  Position: \{show k}
  Input: \{x}
  """

showError (UnexpectedEOI k x) = """
  Unexpected end of input.
  Position: \{show k}
  Input: \{x}
  """

showError (OutOfBounds tp size index) = """
  Index out of bounds.
  \{showOOBTypeErrMsg tp}: \{show size}
  Index: \{show index}
  Note: Indices start at 1.
  """

showError (NoNat x) = "Not a natural number: \{x}"

fromCSV : String -> (n : Nat ** Vect n String)
fromCSV s =
  let cs = forget $ split (',' ==) s
   in (length cs ** fromList cs)

readPrim : Nat -> String -> Either Error (ColType0 b)
readPrim _ "i64"     = Right I64
readPrim _ "str"     = Right Str
readPrim _ "boolean" = Right Boolean
readPrim _ "float"   = Right Float
readPrim _ "bigint"  = Right BigInt
readPrim _ "natural" = Right Natural
readPrim n s         =
  let err = Left $ UnknownType n s
   in case break isDigit s of
        ("fin",r) => maybe err (Right . Finite) $ parsePositive r
        _         => err

readColType : Nat -> String -> Either Error ColType
readColType n s = case reverse $ unpack s of
  '?' :: t        => Optional <$> readPrim n (pack $ reverse t)
  _               => readPrim n s

readSchema : String -> Either Error $ Schema
readSchema s = do
  let primSchema = fromCSV s
  result <- traverse (readColType (fst primSchema)) $ snd primSchema
  Right $ MkSchema _ result

decodeF : (c : ColType0 b) -> String -> Maybe (IdrisType c)
decodeF I64          s  = read s
decodeF Str          s  = read s
decodeF Boolean      s  = read s
decodeF Float        s  = read s
decodeF BigInt       s  = read s
decodeF Natural      s  = read s
decodeF (Finite _)   s  = read s
decodeF (Optional _) "" = Just Nothing
decodeF (Optional t) s  = Just <$> decodeF t s

decodeField : Nat -> (c : ColType) -> String -> Either Error (IdrisType c)
decodeField k c s = maybeToEither (InvalidField k c s) $ decodeF c s

decodeRow : {ts : _} -> String -> Either Error (Row ts)
decodeRow s = go 1 ts.cols $ snd $ fromCSV s
  where go :  Nat
           -> (cs : Vect n ColType)
           -> Vect m String
           -> Either Error $ Row $ MkSchema n cs
        go k Nil       Nil       = Right Nil
        go k Nil       (_ :: _)  = Left $ ExpectedEOI k s
        go k (_ :: _)  Nil       = Left $ UnexpectedEOI k s
        go k (c :: cs) (s :: ss) = [| decodeField k c s :: go (S k) cs ss |]

readFin : {n : _} -> OOBType -> String -> Either Error (Fin n)
readFin tp s = do
  S k <- maybeToEither (NoNat s) $ parsePositive {a = Nat} s
    | Z => Left $ OutOfBounds tp n Z
  maybeToEither (OutOfBounds tp n $ S k) $ natToFin k n

readTblFin : {n : _} -> String -> Either Error (Fin n)
readTblFin = readFin OOBTable

readColFin : {n : _} -> String -> Either Error (Fin n)
readColFin = readFin OOBColumn

readQueryPair :  {t : _}
              -> String
              -> String
              -> Either Error (QueryPair $ schema t)
readQueryPair c v = do
  k <- readColFin c
  p <- decodeField (finToNat k) (index k t.schema.cols) v
  Right (k ** p)

readCommand : {t : Table} -> String -> Either Error (Command t)
readCommand "clear"  =  Right Clear
readCommand "schema" =  Right PrintSchema
readCommand "size"   =  Right PrintSize
readCommand "table"  =  Right PrintTable
readCommand "quit"   =  Right Quit
readCommand s        =  case words s of
  ["new",    str]         => New     <$> readSchema str
  ["delete", str]         => Delete  <$> readTblFin str
  ["get",    str]         => Get     <$> readTblFin str
  ["query", c, v]         => Query   <$> readQueryPair c v
  "add"   :: ss           => Prepend <$> decodeRow (unwords ss)
  _                       => Left     $  UnknownCommand s

encodeField : (t : ColType0 b) -> IdrisType t -> String
encodeField I64          x        = show x
encodeField Str          x        = show x
encodeField Boolean      True     = "t"
encodeField Boolean      False    = "f"
encodeField Float        x        = show x
encodeField BigInt       x        = show x
encodeField Natural      x        = show x
encodeField (Finite _)   x        = show x
encodeField (Optional _) Nothing  = ""
encodeField (Optional t) (Just x) = encodeField t x

encodeRow : (ts : Schema) -> Row ts -> String
encodeRow ts = joinBy "," . go Lin ts
  where go : SnocList String -> (ts : Schema) -> Row ts -> List String
        go sc (MkSchema _ Nil)       Nil       = sc <>> Nil
        go sc (MkSchema _ (c :: cs)) (v :: vs) =
          go (sc :< encodeField c v) (MkSchema _ cs) vs

encodeTable : Table -> String
encodeTable $ MkTable ts _ rs = go Nil ts rs
  where go :  List String -> (cs : Schema) -> Vect _ (Row cs) -> String
        go rs cs Nil       = unlines $ showSchema cs :: rs
        go rs cs (x :: xs) = go (encodeRow cs x :: rs) cs xs

eqIdrisType : IdrisType c -> IdrisType c -> Bool
eqIdrisType t1 t2 = ?rhs

eqColVal : {ts : _} -> Row ts -> QueryPair ts -> Bool
eqColVal rs (c ** v) = eqIdrisType v $ indexRow c rs

queryResult : (t : Table) -> QueryPair (schema t) -> List String
queryResult (MkTable ts n vs) p = go Lin vs
  where go : SnocList String -> Vect _ (Row ts) -> List String
        go sx Nil       = sx <>> Nil
        go sx (x :: xs) =
          let nxt = ifThenElse (eqColVal x p) (sx :< encodeRow ts x) sx
           in go nxt xs

result : (t : Table) -> Command t -> String
result _ $ Clear          = "Table cleared."
result _ $ New ts         = "Created table. Schema: \{showSchema ts}"
result _ $ Delete x       = "Deleted row: \{show $ FS x}"
result _ $ Quit           = "Goodbye."
result t $ PrintSchema    = "Current schema: \{showSchema t.schema}"
result t $ PrintSize      = "Current size: \{show t.size}"
result t $ PrintTable     = "Current table:\n\{encodeTable t}"
result t $ Prepend r      = "Row prepended: \{encodeRow t.schema r}"
result t $ Get x          =
  "Row \{show $ FS x}: \{encodeRow t.schema (index x t.rows)}"
result t $ Query (c ** v) =
  "Query '\{show $ FS c} = \{encodeField (index c t.schema.cols) v}': " ++
  "\{unlines $ queryResult t (c ** v)}"

data Fuel = Dry | More (Lazy Fuel)

runProg : Fuel -> Table -> IO ()
runProg Dry         _ = putStrLn "Ran out of fuel."
runProg (More fuel) t = do
  putStr "Enter a command: "
  str <- getLine
  case readCommand str of
       Left err   => putStrLn (showError err) >> runProg fuel t
       Right Quit => putStrLn (result t Quit)
       Right cmd  => putStrLn (result t cmd) >>
                     runProg fuel (applyCommand t cmd)

covering
forever : Fuel
forever = More $ forever

covering
main : IO ()
main = runProg forever $ MkTable (MkSchema _ Nil) _ Nil

