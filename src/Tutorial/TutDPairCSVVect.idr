module Tutorial.TutDPairCSVVect

import Control.Monad.State

import Data.Either
import Data.Fuel
import Data.HVect
import Data.List1
import Data.String
import Data.Vect

import System.File

import Text.CSV

%default total



--  *** Types ***



data ColType0 : (nullary : Bool) -> Type where
  I64      : ColType0 b
  Str      : ColType0 b
  Boolean  : ColType0 b
  Float    : ColType0 b
  Natural  : ColType0 b
  BigInt   : ColType0 b
  Finite   : Nat -> ColType0 b
  Optional : ColType0 False -> ColType0 True

ColType : Type
ColType = ColType0 True

record Schema where
  constructor MkSchema
  len  : Nat
  cols : Vect len ColType

Semigroup Schema where
  l <+> r = MkSchema _ $ l.cols ++ r.cols

Monoid Schema where
  neutral = MkSchema _ Nil

IdrisType : ColType0 b -> Type
IdrisType $ I64        = Int64
IdrisType $ Str        = String
IdrisType $ Boolean    = Bool
IdrisType $ Float      = Double
IdrisType $ Natural    = Nat
IdrisType $ BigInt     = Integer
IdrisType $ Finite n   = Fin n
IdrisType $ Optional t = Maybe $ IdrisType t

Row : Schema -> Type
Row schema = HVect schema.len $ map IdrisType schema.cols

record Table where
  constructor MkTable
  schema : Schema
  size   : Nat
  rows   : Vect size (Row schema)

data Error : Type where
  ExpectedEOI    : (pos : Nat) -> String -> Error
  ExpectedLine   : Error
  InvalidCell    : (row, col : Nat) -> ColType0 b -> String -> Error
  NoNat          : String -> Error
  OutOfBounds    : (size : Nat) -> (index : Nat) -> Error
  ReadError      : (path : String) -> FileError -> Error
  UnexpectedEOI  : (pos : Nat) -> String -> Error
  UnknownCommand : String -> Error
  UnknownType    : (pos : Nat) -> String -> Error
  WriteError     : (path : String) -> FileError -> Error

data Command : (t : Table) -> Type where
  PrintSchema : Command t
  PrintSize   : Command t
  PrintTable  : Command t
  Save        : Command t
  Load        : Table -> Command t
  New         : (newSchema : Schema) -> Command t
  Prepend     : Row t.schema -> Command t
  Get         : Fin t.size -> Command t
  Delete      : Fin t.size -> Command t
  Quit        : Command t
  Query       :  (ix : Fin (t.schema.len))
              -> (val : IdrisType $ indexVect t.schema.cols ix)
              -> Command t



--  *** Core Functionality ***



eq : (c : ColType0 b) -> IdrisType c -> IdrisType c -> Bool
eq I64          x        y        = x == y
eq Str          x        y        = x == y
eq Boolean      x        y        = x == y
eq Float        x        y        = x == y
eq Natural      x        y        = x == y
eq BigInt       x        y        = x == y
eq (Finite _)   x        y        = x == y
eq (Optional z) (Just x) (Just y) = eq z x y
eq (Optional _) Nothing  Nothing  = True
eq (Optional _) _        _        = False

eqAt :  (ts  : Schema)
     -> (ix  : Fin $ ts.len)
     -> (val : IdrisType $ indexVect ts.cols ix)
     -> (row : Row ts)
     -> Bool
eqAt (MkSchema _ (x :: _))  FZ     val (v :: _)  = eq x val v
eqAt (MkSchema _ (_ :: xs)) (FS y) val (_ :: vs) = eqAt (MkSchema _ xs) y val vs
eqAt (MkSchema _ Nil)       _      _   _         impossible

applyCommand : (t : Table) -> Command t -> Table
applyCommand t                 PrintSchema    = t
applyCommand t                 PrintSize      = t
applyCommand t                 PrintTable     = t
applyCommand t                 Save           = t
applyCommand _                 (Load t')      = t'
applyCommand _                 (New ts)       = MkTable ts _ Nil
applyCommand (MkTable ts n rs) (Prepend r)    = MkTable ts _ $ r :: rs
applyCommand t                 (Get x)        = t
applyCommand t                 Quit           = t
applyCommand t                 (Query ix val) = t
applyCommand (MkTable ts n rs) (Delete x)     = case n of
  S k => MkTable ts k $ deleteAt x rs
  Z   => absurd x



--  *** Parsers ***



zipWithIndex : Traversable t => t a -> t (Nat, a)
zipWithIndex = evalState 1 . traverse pairWithIndex
  where pairWithIndex : a -> State Nat (Nat,a)
        pairWithIndex v = (,v) <$> get <* modify S

fromCSV : String -> (n : Nat ** Vect n String)
fromCSV str =
  let vec = fromList $ forget $ split (',' ==) str
   in (_ ** vec)

readPrim : Nat -> String -> Either Error (ColType0 b)
readPrim _ "i64"     = Right I64
readPrim _ "str"     = Right Str
readPrim _ "boolean" = Right Boolean
readPrim _ "float"   = Right Float
readPrim _ "natural" = Right Natural
readPrim _ "bigint"  = Right BigInt
readPrim n s         =
  let err = Left $ UnknownType n s
   in case break isDigit s of
        ("fin",r) => maybe err (Right . Finite) $ parsePositive r
        _         => err

readColType : Nat -> String -> Either Error ColType
readColType n s = case reverse $ unpack s of
  '?' :: t => Optional <$> readPrim n (pack $ reverse t)
  _        => readPrim n s

toSchema : {n : Nat} -> Vect n ColType -> Schema
toSchema ts = MkSchema n ts

readSchema : String -> Either Error Schema
readSchema s =
  [| toSchema
   $ traverse (uncurry readColType)
   $ zipWithIndex
   $ snd (fromCSV s) |]

readSchemaList : List String -> Either Error Schema
readSchemaList [s] = readSchema s
readSchemaList _   = Left ExpectedLine

decodeF : (c : ColType0 b) -> String -> Maybe (IdrisType c)
decodeF I64          s  = read s
decodeF Str          s  = read s
decodeF Boolean      s  = read s
decodeF Float        s  = read s
decodeF Natural      s  = read s
decodeF BigInt       s  = read s
decodeF (Finite _)   s  = read s
decodeF (Optional _) "" = Just Nothing
decodeF (Optional t) s  = Just <$> decodeF t s

decodeField :  (row,col : Nat)
            -> (c : ColType0 b)
            -> String
            -> Either Error (IdrisType c)
decodeField cell k c s = maybeToEither (InvalidCell cell k c s) $ decodeF c s

decodeRow : {ts : _} -> (row : Nat) -> String -> Either Error (Row ts)
decodeRow row s = go 1 ts.cols $ snd $ fromCSV s
  where go :  Nat
           -> (cs : Vect n ColType)
           -> Vect m String
           -> Either Error (Row $ MkSchema n cs)
        go k Nil       Nil       = Right Nil
        go k Nil       (_ :: _)  = Left $ ExpectedEOI k s
        go k (_ :: _)  Nil       = Left $ UnexpectedEOI k s
        go k (c :: cs) (s :: ss) = [| decodeField row k c s :: go (S k) cs ss |]

decodeRows : {ts : _} -> List String -> Either Error (List $ Row ts)
decodeRows = traverse (uncurry decodeRow) . zipWithIndex

readFin : {n : _} -> String -> Either Error (Fin n)
readFin s = do
  S k <- maybeToEither (NoNat s) $ parsePositive s
    | Z => Left $ OutOfBounds n Z
  maybeToEither (OutOfBounds n $ S k) $ natToFin k n

readCommand : (t : Table) -> String -> Either Error (Command t)
readCommand _ "schema" = Right PrintSchema
readCommand _ "size"   = Right PrintSize
readCommand _ "table"  = Right PrintTable
readCommand _ "quit"   = Right Quit
readCommand t s        = case words s of
  ["new",    str]    => New     <$> readSchema str
  "add" ::   ss      => Prepend <$> decodeRow 1 (unwords ss)
  ["get",    str]    => Get     <$> readFin str
  ["delete", str]    => Delete  <$> readFin str
  "query" :: n :: ss => do
    ix  <- readFin n
    val <- decodeField 1 1 (indexVect t.schema.cols ix) $ unwords ss
    pure $ Query ix val
  _                  => Left     $  UnknownCommand s



--  *** Printers ***



toCSV : Vect n String -> String
toCSV = concat . intersperse ","

showColType : ColType0 b -> String
showColType $ I64        = "i64"
showColType $ Str        = "str"
showColType $ Boolean    = "boolean"
showColType $ Float      = "float"
showColType $ Natural    = "natural"
showColType $ BigInt     = "bigint"
showColType $ Finite n   = "fin\{show n}"
showColType $ Optional t = "\{showColType t}?"

encodeField : (t : ColType0 b) -> IdrisType t -> String
encodeField I64          x        = show x
encodeField Str          x        = x
encodeField Boolean      True     = "t"
encodeField Boolean      False    = "f"
encodeField Float        x        = show x
encodeField Natural      x        = show x
encodeField BigInt       x        = show x
encodeField (Finite _)   x        = show x
encodeField (Optional y) (Just v) = encodeField y v
encodeField (Optional _) Nothing  = ""

encodeFields : (ts : Schema) -> Row ts -> Vect ts.len String
encodeFields (MkSchema _ Nil)       Nil       = Nil
encodeFields (MkSchema _ (c :: cs)) (v :: vs) =
  encodeField c v :: encodeFields (MkSchema _ cs) vs

encodeTable : Table -> String
encodeTable $ MkTable ts _ rs =
  unlines . toList $ map (toCSV . encodeFields ts) rs

encodeSchema : Schema -> String
encodeSchema schema = toCSV $ map showColType schema.cols

-- TODO: Numeric Types Right-Aligned
prettyTable :  {n : _}
            -> (header : Vect n String)
            -> (table  : Vect m (Vect n String))
            -> String
prettyTable h t =
  let ls  = foldl (zipWith $ \k => max k . length) (replicate n Z) (h :: t)
      bar = concat . intersperse "---" $ map (`replicate` '-') ls
   in unlines . toList $ line ls h :: bar :: map (line ls) t

  where pad : Nat -> String -> String
        pad v = padRight v ' '

        line : Vect n Nat -> Vect n String -> String
        line lengths = concat . intersperse " | " . zipWith pad lengths

printTable :  (cs   : Schema)
           -> (rows : Vect n (Row cs))
           -> String
printTable cs rs =
  let header  = map showColType cs.cols
      table   = map (encodeFields cs) rs
   in prettyTable header table

allTypes : String
allTypes = concat
         . List.intersperse ", "
         . map (showColType {b = True})
         $ [I64,Str,Boolean,Float]

showError : Error -> String
showError (ExpectedEOI k x) = """
  Expected end of input.
  Position: \{show k}
  Input: \{x}
  """

showError ExpectedLine = """
  Error when reading schema.
  Expected a single line of content.
  """

showError (InvalidCell row col tpe x) = """
  Invalid value at row \{show row}, column \{show col}.
  Expected type: \{showColType tpe}.
  Value found: \{x}.
  """

showError (NoNat x) = "Not a natural number: \{x}"

showError (OutOfBounds size index) = """
  Index out of bounds.
  Size of table: \{show size}
  Index: \{show index}
  Note: Indices start at zero.
  """

showError (ReadError path err) = """
  Error when reading file \{path}.
  Message: \{show err}
  """

showError (UnexpectedEOI k x) = """
  Unexpected end of input.
  Position: \{show k}
  Input: \{x}
  """

showError (UnknownCommand x) = """
  Unknown command: \{x}.
  Known commands are: clear, schema, size, table, new, add, get, delete, quit.
  """

showError (UnknownType pos x) = """
  Unknown type at position \{show pos}: \{x}.
  Known types are: \{allTypes}.
  """

showError (WriteError path err) = """
  Error when writing file \{path}.
  Message: \{show err}
  """

result : (t : Table) -> Command t -> String
result t $ PrintSchema    = "Current schema: \{encodeSchema t.schema}"
result t $ PrintSize      = "Current size: \{show t.size}"
result t $ PrintTable     = "Table:\n\n\{printTable t.schema t.rows}"
result _ $ Save           = "Table written to disk."
result _ $ Load t'        = "Table loaded. Schema: \{encodeSchema t'.schema}"
result _ $ New ts         = "Created table. Schema: \{encodeSchema ts}"
result t $ Prepend r      = "Row prepended:\n\n\{printTable t.schema [r]}"
result _ $ Quit           = "Goodbye."
result _ $ Delete x       = "Deleted row: \{show $ FS x}"
result t $ Query ix val   =
  let (_ ** rs) = filter (eqAt t.schema ix val) t.rows
   in "Result:\n\n\{printTable t.schema rs}"
result t $ Get x          =
  "Row \{show $ FS x}:\n\n\{printTable t.schema [index x t.rows]}"



--  *** File IO ***



readFileSafe : HasIO io => Fuel -> String -> io (Either FileError String)
readFileSafe = go Nil $ Just Z
  where go :  (lines : List String)
           -> (offset : Maybe Nat)
           -> (fuel : Fuel)
           -> (path : String)
           -> io (Either FileError String)
        go lines Nothing       _           _    = pure $ Right $ unlines lines
        go lines _             Dry         _    = pure $ Right $ unlines lines
        go lines (Just offset) (More fuel) path = do
          Right (eof, fLines) <- readFilePage offset (limit 10) path
            | Left err => pure $ Left err
          go (lines ++ fLines) (toMaybe (not eof) $ offset + 10) fuel path

load :  Monoid a
     => (fuel : Fuel)
     -> (path : String)
     -> (decode : List String -> Either Error a)
     -> IO (Either Error a)
load Dry         _    _      = pure $ pure neutral
load (More fuel) path decode = do
  Right ls <- readFileSafe fuel path
    | Left err => pure $ Left (ReadError path err)
  pure $ decode (filter (not . null) $ lines ls)

write : (path : String) -> (content : String) -> IO (Either Error ())
write path content = mapFst (WriteError path) <$> writeFile path content

namespace IOEither
  export
  (>>=) : IO (Either err a) -> (a -> IO (Either err b)) -> IO (Either err b)
  (>>=) ioa f = Prelude.(>>=) ioa $ either (pure . Left) f

  export
  (>>) : IO (Either err ()) -> Lazy (IO (Either err b)) -> IO (Either err b)
  (>>) x y = x >>= const y

  export
  pure : a -> IO (Either err a)
  pure = Prelude.pure . Prelude.pure

readCommandIO : Fuel -> (t : Table) -> String -> IO (Either Error (Command t))
readCommandIO Dry         _ _ = Prelude.pure $ Right Quit
readCommandIO (More fuel) t s = case words s of
  ["save", pth] => IOEither.do
    write (pth ++ ".schema") (encodeSchema t.schema)
    write (pth ++ ".csv") (encodeTable t)
    pure Save

  ["load", pth] => IOEither.do
    schema <- load fuel (pth ++ ".schema") readSchemaList
    rows   <- load fuel (pth ++ ".csv") (decodeRows {ts = schema})
    pure . Load $ MkTable schema (length rows) (fromList rows)

  _ => Prelude.pure $ readCommand t s



--  *** Main Loop ***



runProg : Fuel -> Table -> IO ()
runProg Dry         t = putStrLn "Ran out of fuel. \{result t Quit}"
runProg (More fuel) t = do
  putStr "Enter a command: "
  str <- getLine
  cmd <- readCommandIO fuel t str
  case cmd of
    Left  err  => putStrLn (showError err) >> runProg fuel t
    Right Quit => putStrLn (result t Quit)
    Right cmd  => putStrLn (result t cmd) >>
                  runProg fuel (applyCommand t cmd)

covering
main : IO ()
main = runProg forever $ MkTable (MkSchema _ Nil) _ Nil

