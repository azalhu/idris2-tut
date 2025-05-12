module Tut2

import Data.List
import Data.String

%default total

phi : (a : p -> q -> r) ->
      (b : y -> p) ->
      (c : y -> q) ->
      (d : y) -> r
phi a b c d = a (b d) (c d)

record Artist where
  constructor MkArtist
  name : String

record Album where
  constructor MkAlbum
  name : String
  artist : Artist

record Email where
  constructor MkEmail
  value : String

record Password where
  constructor MkPassword
  value : String

record User where
  constructor MkUser
  name : String
  email : Email
  password : Password
  albums : List Album

Eq Artist where
  (==) = (==) `on` name

Eq Album where
  (==) = (==) `on` phi MkPair name artist

Eq Email where
  (==) = (==) `on` value

Eq Password where
  (==) = (==) `on` value

Eq User where
  (==) = on (==)
       $ phi MkPair name
       $ phi MkPair email
       $ phi MkPair password
       $            albums

record Credentials where
  constructor MkCredentials
  email : Email
  password : Password

record Request where
  constructor MkRequest
  credentials : Credentials
  album : Album

data Response : Type where
  UnknownUser : Email -> Response
  InvalidPassword : Response
  AccessDenied : Email -> Album -> Response
  Success : Album -> Response

DB : Type
DB = List User

handleRequest : DB -> Request -> Response
handleRequest db (MkRequest (MkCredentials e pw) album) =
  case find ((e ==) . email) db of
       Nothing => UnknownUser e
       Just (MkUser _ _ password albums)
       => if password /= pw
             then InvalidPassword
             else if elem album albums
                     then Success album
                     else AccessDenied e album

--handleRequest : DB -> Request -> Response
--handleRequest db (MkRequest (MkCredentials email pw) album) =
--  case lookupUser db of
--       Just (MkUser _ _ password albums)
--       => if password == pw
--             then lookupAlbum albums
--             else InvalidPassword
--       Nothing => UnknownUser email
--  where lookupUser : List User -> Maybe User
--        lookupUser [] = Nothing
--        lookupUser (x :: xs) =
--          if x.email == email
--             then Just x
--             else lookupUser xs
--
--        lookupAlbum : List Album -> Response
--        lookupAlbum [] = AccessDenied email album
--        lookupAlbum (x :: xs) =
--          if x == album
--             then Success album
--             else lookupAlbum xs

data Nucleobase = A | G | C | T

DNA : Type
DNA = List Nucleobase

readBase : Char -> Maybe Nucleobase
readBase 'A' = Just A
readBase 'G' = Just G
readBase 'C' = Just C
readBase 'T' = Just T
readBase _ = Nothing

traverseList : (a -> Maybe b) -> List a -> Maybe (List b)
traverseList _ [] = Just []
traverseList f (x :: xs) =
  case f x of
       Just y => case traverseList f xs of
                      Just ys => Just (y :: ys)
                      Nothing => Nothing
       Nothing => Nothing

readDNA : String -> Maybe DNA
readDNA = traverseList readBase . unpack

complement : DNA -> DNA
complement = map comp
  where comp : Nucleobase -> Nucleobase
        comp A = T
        comp G = C
        comp C = G
        comp T = A

fromMaybe : (deflt : a) -> (ma : Maybe a) -> a
fromMaybe deflt Nothing = deflt
fromMaybe _ (Just x) = x

extractBool : Maybe Bool -> Bool
extractBool v = fromMaybe { ma = v, deflt = False }

extractBool2 : Maybe Bool -> Bool
extractBool2 = fromMaybe { deflt = False }

record Dragon where
  constructor MkDragon
  name : String
  strength : Nat
  hitPoints : Int16

gorgar : Dragon
gorgar = MkDragon { strength = 150, name = "Gorgar", hitPoints = 10000 }

IntOrString : Bool -> Type
IntOrString True = Integer
IntOrString False = String

intOrString : (v : Bool) -> IntOrString v
intOrString False = "I'm a String"
intOrString True = 1000

toBool : {v : _} -> IntOrString v -> Bool
toBool {v = True} _ = True
toBool {v = False} _ = False

maybeToEither : {0 a : Type} -> Maybe a -> Either String a
maybeToEither Nothing = Left "Nope"
maybeToEither (Just x) = Right x

maybeToEither' : Maybe a -> Either String a
maybeToEither' Nothing = Left "Nope"
maybeToEither' (Just x) = Right x

