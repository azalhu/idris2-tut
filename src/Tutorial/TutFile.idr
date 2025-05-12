module Tutorial.TutFile

import Data.String
import System.File

%default total

phi : (a : p -> q -> r) ->
      (b : y -> p) ->
      (c : y -> q) ->
      (x : y) -> r
phi a b c x = a (b x) (c x)

covering
countEmpty : (path : String) -> IO (Either FileError Nat)
countEmpty path = openFile path Read >>= either (pure . Left) (go 0)
  where go : Nat -> File -> IO (Either FileError Nat)
        go k file = do
          False <- fEOF file | True => closeFile file $> Right k
          Right "\n" <- fGetLine file
            | Right _  => go k file
            | Left err => closeFile file $> Left err
          go (S k) file

covering
countEmpty' : (path : String) -> IO (Either FileError Nat)
countEmpty' path = withFile path Read pure (go 0)
  where go : Nat -> File -> IO (Either FileError Nat)
        go k file = do
          False <- fEOF file | True => pure $ Right k
          Right "\n" <- fGetLine file
            | Right _  => go k file
            | Left err => pure $ Left err
          go (S k) file

namespace IOErr
  export
  pure : a -> IO (Either e a)
  pure = pure . Right

  export
  fail : e -> IO (Either e a)
  fail = pure . Left

  export
  lift : IO a -> IO (Either e a)
  lift = map Right

  export
  catch : IO (Either e1 a) -> (e1 -> IO (Either e2 a)) -> IO (Either e2 a)
  catch io f = do
    Left err <- io | Right v => pure v
    f err

  export
  (>>=) : IO (Either e a) -> (a -> IO (Either e b)) -> IO (Either e b)
  (>>=) io f = Prelude.do
    Right v <- io | Left err => fail err
    f v

  export
  (>>) : IO (Either e ()) -> Lazy (IO (Either e b)) -> IO (Either e b)
  (>>) iou ioa = Prelude.do
    Right _ <- iou | Left err => fail err
    ioa

covering
countEmpty'' : (path : String) -> IO (Either FileError Nat)
countEmpty'' path = withFile path Read pure (go 0)
  where go : Nat -> File -> IO (Either FileError Nat)
        go k file = do
          False <- lift (fEOF file) | True => pure k
          "\n"  <- fGetLine file    | _ => go k file
          go (S k) file

covering
countWords : (path : String) -> IO (Either FileError Nat)
countWords path = withFile path Read pure (go 0)
  where go : Nat -> File -> IO (Either FileError Nat)
        go k file = do
          False <- lift (fEOF file) | True => pure k
          line  <- fGetLine file
          go (k + length (words line)) file

covering
withLines :  (path : String)
          -> (accum : s -> String -> s)
          -> (initialState : s)
          -> IO (Either FileError s)
withLines path accum initialState = withFile path Read pure (go initialState)
  where go : s -> File -> IO (Either FileError s)
        go k file = do
          False <- lift (fEOF file) | True => pure k
          line  <- fGetLine file
          go (accum k line) file

covering
countWithLines :  (accum : Nat -> String -> Nat)
               -> (path : String)
               -> IO (Either FileError Nat)
countWithLines accum path = withLines path accum 0

covering
countEmptyWithLines : (path : String) -> IO (Either FileError Nat)
countEmptyWithLines =
  countWithLines (\k, line => if line == "\n" then S k else k)

covering
countWordsWithLines : (path : String) -> IO (Either FileError Nat)
countWordsWithLines =
  countWithLines (\k, line => k + length (words line))

covering
foldLines :  Monoid s
          => (path : String)
          -> (f    : String -> s)
          -> IO (Either FileError s)
foldLines path f = withLines path (\k => (k <+>) . f) neutral

record FileCount where
  constructor MkFileCount
  fileLines      : Nat
  fileWords      : Nat
  fileCharacters : Nat

Semigroup FileCount where
  (<+>) (MkFileCount lc1 wc1 cc1) (MkFileCount lc2 wc2 cc2) =
    MkFileCount (lc1 + lc2) (wc1 + wc2) (cc1 + cc2)

Monoid FileCount where
  neutral = MkFileCount Z Z Z

Show FileCount where
  showPrec d (MkFileCount lc wc cc) =
    showCon d "MkFileCount" ("\{showArg lc} lines," ++ "\{showArg wc} words," ++ "\{showArg cc} characters")

covering
wordCount : (path : String) -> IO (Either FileError FileCount)
wordCount = flip foldLines $ phi (MkFileCount (S Z)) (length . words) length

covering
testWordCount : (path : String) -> IO ()
testWordCount path = do
  Right wc <- wordCount path | Left err => putStrLn "Error: \{show err}"
  putStrLn (show wc)

