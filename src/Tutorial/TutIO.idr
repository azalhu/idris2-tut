module Tutorial.TutIO

import Data.List1
import Data.String
import Data.Vect

%default total

phi : (a : p -> q -> r) ->
      (b : y -> p) ->
      (c : y -> q) ->
      (x : y) -> r
phi a b c x = a (b x) (c x)

hello: IO ()
hello = putStrLn "Hello World!"

readHello : IO ()
readHello = do
  name <- getLine
  putStrLn $ "Hello \{name}!"

launchMissiles : IO ()
launchMissiles = putStrLn "Boom! You're dead."

friendlyReadHello : IO ()
friendlyReadHello = do
  putStrLn "Please enter your name."
  readHello

actions : Vect 3 (IO ())
actions = [launchMissiles, friendlyReadHello, friendlyReadHello]

runActions : Vect (S n) (IO ()) -> IO ()
runActions (_ :: xs) = go xs
  where go : Vect k (IO ()) -> IO ()
        go [] = pure ()
        go (y :: ys) = do
          y
          go ys

readHellos : IO ()
readHellos = runActions actions

data Error : Type where
  NotAnInteger : (value : String) -> Error
  UnknownOperator : (value : String) -> Error
  ParseError : (value :String) -> Error

Show Error where
  show (NotAnInteger v) = "Not an integer: \{v}."
  show (UnknownOperator v) = "Unknown operator: \{v}."
  show (ParseError v) = "Invalid expression: \{v}."

readInteger : String -> Either Error Integer
readInteger s = maybe (Left $ NotAnInteger s) Right $ parseInteger s

readOperator : String -> Either Error (Integer -> Integer -> Integer)
readOperator "+" = Right (+)
readOperator "*" = Right (*)
readOperator s = Left $ UnknownOperator s

eval : String -> Either Error Integer
eval s =
  let [x,y,z]  := forget $ split isSpace s | _ => Left (ParseError s)
      Right v1 := readInteger x  | Left e => Left e
      Right op := readOperator y | Left e => Left e
      Right v2 := readInteger z  | Left e => Left e
   in Right $ op v1 v2

evalDo' : String -> Either Error Integer
evalDo' s = do
  let [x,y,z] := forget $ split isSpace s | _ => Left (ParseError s)
  v1 <- readInteger x
  op <- readOperator y
  v2 <- readInteger z
  Right $ op v1 v2

evalDo : String -> Either Error Integer
evalDo s = case forget $ split isSpace s of
  [x,y,z] => do
    v1 <- readInteger x
    op <- readOperator y
    v2 <- readInteger z
    Right $ op v1 v2
  _       => Left (ParseError s)

exprProg : IO ()
exprProg = do
  s <- getLine
  case eval s of
       Left err  => putStrLn "An error occured:\n\{show err}"
       Right res => putStrLn "\{s} = \{show res}"

rep : (String -> String) -> IO ()
rep f = do
  s <- getLine
  let res = f s
  putStrLn res

covering
repl : (String -> String) -> IO ()
repl f = do
  s <- getLine
  let res = f s
  putStrLn res
  repl f

covering
replTill : (String -> Either String String) -> IO ()
replTill f = do
  s <- getLine
  let Right res = f s
    | Left err => putStrLn err
  putStrLn res
  replTill f

covering
exprRepl : IO ()
exprRepl = do
  let f : String -> Either String String
      f s = if s == "done"
               then Left "Bye for now!"
               else case eval s of
                         Left err  => Right "An error occured:\n\{show err}"
                         Right res => Right "\{s} = \{show res}"
  replTill f

covering
replWith :  (state      : s)
         -> (next       : s -> String -> Either res s)
         -> (dispState  : s -> String)
         -> (dispResult : res -> s -> String)
         -> IO ()
replWith state next dispState dispResult = do
  putStr $ dispState state
  input <- getLine
  let Right next_state = next state input
    | Left res => putStrLn $ dispResult res state
  replWith next_state next dispState dispResult

data Result = InvalidInput String | Done

Show Result where
  show (InvalidInput input) = "Invalid input: \{input}"
  show Done = "Bye for now! :)"

covering
sumNumbers : IO ()
sumNumbers = do
  let initial_state : Nat
      initial_state = Z

      next : (state : Nat) -> (input : String) -> Either Result Nat
      next _ "done" = Left Done
      next state input =
        let Just integer = parsePositive input
          | Nothing => Left $ InvalidInput input
         in Right $ state + integerToNat integer

      dispState : Nat -> String
      dispState state = "Current sum: \{show state}\nPlease enter a number: "

      dispResult : Result -> Nat -> String
      dispResult res state = "\{show res}\nFinal sum: \{show state}"

  replWith initial_state next dispState dispResult

flatten : Vect m (Vect n a) -> Vect (m * n) a
flatten [] = []
flatten (x :: xs) = x ++ flatten xs

(>>=) : Vect m a -> (a -> Vect n b) -> Vect (m * n) b
(>>=) = flatten .: flip map

modString : String -> Vect 4 String
modString s = [s, reverse s, toUpper s, toLower s]

testDo : Vect 24 String
testDo = do
  s1 <- ["Hello", "World"]
  s2 <- [1, 2, 3]
  modString (s1 ++ show s2)

testDo' : Vect 24 String
testDo' =
  ["Hello", "World"] >>= (\s1 =>
    [1, 2, 3] >>= (\s2 =>
      modString (s1 ++ show s2)
    )
  )

testDo'' : Vect 24 String
testDo'' =
  flatten (flip map ["Hello", "World"] (\s1 =>
    flatten (flip map [1, 2, 3] (\s2 =>
      modString (s1 ++ show s2)
    ))
  ))

namespace Foo
  export
  eval : Nat -> Nat -> Nat
  eval = (*)

-- prefixing `eval` with its namespace is not strictly necessary here
testFooEval : Nat
testFooEval = Foo.eval 12 100

getHello : IO ()
getHello = putStrLn $ "Hello \{!getLine}!"

getHello' : IO ()
getHello' = do
  s <- getLine
  putStrLn "Hello \{s}!"

bangExpr : String -> String -> String -> Maybe Integer
bangExpr s1 s2 s3 =
  Just $ !(parseInteger s1) + !(parseInteger s2) + !(parseInteger s3)

bangExpr' : String -> String -> String -> Maybe Integer
bangExpr' s1 s2 s3 = do
  x1 <- parseInteger s1
  x2 <- parseInteger s2
  x3 <- parseInteger s3
  Just $ x1 + x2 + x3

ex1a : IO String
ex1a = do
  s1 <- getLine
  s2 <- getLine
  s3 <- getLine
  pure $ s1 ++ reverse s2 ++ s3

ex1a' : IO String
ex1a' = pure $ !getLine ++ reverse !getLine ++ !getLine

ex1a'' : IO String
ex1a'' =
  getLine >>= (\s1 =>
    getLine >>= (\s2 =>
      getLine >>= (\s3 =>
        pure $ s1 ++ reverse s2 ++ s3
      )
    )
  )

ex1b : Maybe Integer
ex1b = do
  n1 <- parseInteger "12"
  n2 <- parseInteger "300"
  pure $ n1 + n2 * 100

ex1b' : Maybe Integer
ex1b' = pure $ !(parseInteger "12") + !(parseInteger "300") * 100

ex1b'' : Maybe Integer
ex1b'' =
  parseInteger "12" >>= (\n1 =>
    parseInteger "300" >>= (\n2 =>
      pure $ n1 + n2 * 100
    )
  )

data List01 : (nonEmpty : Bool) -> Type -> Type where
  Nil  : List01 False a
  (::) : a -> List01 False a -> List01 ne a

head : List01 True a -> a
head (x :: _) = x

weaken : List01 ne a -> List01 False a
weaken Nil = Nil
weaken (x :: xs) = x :: xs

tail : List01 True a -> List01 False a
tail (_ :: xs) = xs

(++) : List01 b1 a -> List01 b2 a -> List01 (b1 || b2) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: xs ++ weaken ys

concat' : List01 ne1 (List01 ne2 a) -> List01 False a
concat' Nil       = Nil
concat' (x :: xs) = weaken $ x ++ concat' xs

concat :  {ne1, ne2 : _}
       -> List01 ne1 (List01 ne2 a)
       -> List01 (ne1 && ne2) a
concat {ne1 = True}  {ne2 = True}  = phi (++) head (concat' . tail)
concat {ne1 = True}  {ne2 = False} = concat'
concat {ne1 = False} {ne2 = _}     = concat'

map01 : (a -> b) -> List01 ne a -> List01 ne b
map01 f Nil       = Nil
map01 f (x :: xs) = f x :: map01 f xs

namespace List01
  export
  (>>=) :  {ne1, ne2 : _}
        -> List01 ne1 a
        -> (a -> List01 ne2 b)
        -> List01 (ne1 && ne2) b
  (>>=) = concat .: flip map01

-- this and lf are necessary to make sure, which tag to use
-- when using list literals
lt : List01 True a -> List01 True a
lt = id

lf : List01 False a -> List01 False a
lf = id

test : List01 True Integer
test = do
  x  <- lt [1, 2, 3]
  y  <- lt [4, 5, 6, 7]
  op <- lt [(*), (+), (-)]
  [op x y]

test2 : List01 False Integer
test2 = do
  x  <- lt [1, 2, 3]
  y  <- lf Nil
  op <- lt [(*), (+), (-)]
  lt [op x y]

