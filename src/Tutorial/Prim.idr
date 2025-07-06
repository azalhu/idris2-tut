module Tutorial.Prim

import Data.Bits
import Data.String

%default total



--  ****** How Primitives are Implemented ******



--  *** Consequences of being Primitive ***



covering
replicateBits8' : Bits8 -> a -> List a
replicateBits8' 0 _ = Nil
replicateBits8' n v = v :: replicateBits8' (n - 1) v

replicateBits8 : Bits8 -> a -> List a
replicateBits8 0 _ = Nil
replicateBits8 n v = v :: replicateBits8 (assert_smaller n $ n - 1) v

zeroBits8 : the Bits8 0 = 255 + 1
zeroBits8 = Refl

data LenList : (n : Nat) -> Type -> Type where
  MkLenList : (as : List a) -> LenList (length as) a

0 concatLen : (xs,ys : List a) -> length xs + length ys = length (xs ++ ys)
concatLen Nil       ys = Refl
concatLen (x :: xs) ys = cong S $ concatLen xs ys

(++) : LenList m a -> LenList n a -> LenList (m + n) a
MkLenList xs ++ MkLenList ys = rewrite concatLen xs ys in MkLenList (xs ++ ys)

0 concatLenStr : (a,b : String) -> length a + length b = length (a ++ b)



--  *** Believe Me! ***



concatLenStr a b = believe_me $ Refl {x = length a + length b}

0 doubleAddAssoc : (x,y,z : Double) -> x + (y + z) = (x + y) + z
doubleAddAssoc x y z = believe_me $ Refl {x = x + (y + z)}

Tiny : Double
Tiny = 0.0000000000000001

One : Double
One = 1.0

--wrong : (0 _ : 1.00000000000000033306 = 1.0) -> Void
wrong : (0 _ : 1.0000000000000002 = 1.0) -> Void
wrong Refl impossible

boom : Void
boom = wrong $ doubleAddAssoc One Tiny Tiny

tailExample : prim__strTail "foo" = "oo"
tailExample = Refl



--  ****** Working with Strings ******



--  *** String Interpolation ***

interpEx1 : Bits64 -> Bits64 -> String
interpEx1 x y = "\{show x} + \{show y} = \{show $ x + y}"

data Element = H | He | C | N | O | F | Ne

Formula : Type
Formula = List (Element,Nat)

Interpolation Element where
  interpolate H  = "H"
  interpolate He = "He"
  interpolate C  = "C"
  interpolate N  = "N"
  interpolate O  = "O"
  interpolate F  = "F"
  interpolate Ne = "Ne"

Interpolation (Element,Nat) where
  interpolate (_, 0) = ""
  interpolate (x, 1) = "\{x}"
  interpolate (x, k) = "\{x}\{show k}"

Interpolation Formula where
  interpolate = foldMap interpolate

ethanol : String
ethanol = "The formula of ethanol is: \{[(C,2),(H,6),(O, the Nat 1)]}"



--  *** Raw and Multiline String Literals ***



escapeExample : String
escapeExample = "A quote: \". \nThis is on a new line.\nA backslash: \\"

rawExample : String
rawExample = #"A quote: ". A blackslash [sic]: \"#

rawExample2 : String
rawExample2 = ##"A quote: ". A blackslash [sic]: \"##

rawInterpolExample : String
rawInterpolExample = ##"An interpolated "string": \##{rawExample}"##

multiline1 : String
multiline1 = """
  And I raise my head and stare
  Into the eyes of a stranger
  I've always known that the mirror never lies
  People always turn away
  From the eyes of a stranger
  Afraid to see what hides behind the stare
  """

multiline2 : String
multiline2 = #"""
  An example for a simple expression:
  "foo" ++ "bar".
  This is reduced to "\#{"foo" ++ "bar"}".
  """#



--  *** Exercises part 1 ***



accChar : Char -> Char
accChar = cast . (+1) . cast

betweenChars : Char -> Char -> Char -> Bool
betweenChars cMin cMax c = (cMin <= c) && (c <= cMax)

accBetweenChars : Char -> Char -> Char -> Maybe Char
accBetweenChars cMin cMax c = case betweenChars cMin cMax c of
  True  => Just $ accChar c
  False => Nothing

mapString : (f : Char -> Char) -> String -> String
mapString f = pack . go Lin . unpack
  where go : SnocList Char -> List Char -> List Char
        go acc Nil       = acc <>> Nil
        go acc (c :: cs) = go (acc :< f c) cs

filterString : (f : Char -> Bool) -> String -> String
filterString f = pack . go Lin . unpack
  where go : SnocList Char -> List Char -> List Char
        go acc Nil       = acc <>> Nil
        go acc (c :: cs) = case f c of
          True  => go (acc :< c) cs
          False => go acc cs

mapMaybeString : (f : Char -> Maybe Char) -> String -> String
mapMaybeString f = pack . go Lin . unpack
  where go : SnocList Char -> List Char -> List Char
        go acc Nil       = acc <>> Nil
        go acc (c :: cs) = case f c of
          Just p  => go (acc :< p) cs
          Nothing => go acc cs

foldlString : (f : acc -> Char -> acc) -> acc -> String -> acc
foldlString f a = go a . unpack
  where go : acc -> List Char -> acc
        go ac Nil       = ac
        go ac (c :: cs) = go (f ac c) cs

foldMapString : Monoid m => (Char -> m) -> String -> m
foldMapString f = go neutral . unpack
  where go : m -> List Char -> m
        go acc Nil       = acc
        go acc (c :: cs) = go (acc <+> f c) cs

traverseString' : Applicative f => (Char -> f Char) -> String -> f String
traverseString' g s = [| pack $ go $ unpack s |]
  where go : List Char -> f (List Char)
        go Nil       = pure Nil
        go (c :: cs) = [| g c :: go cs |]

traverseString : Applicative f => (Char -> f Char) -> String -> f String
traverseString g s = [| pack $ go (pure Lin) $ unpack s |]
  where go : f (SnocList Char) -> List Char -> f (List Char)
        go acc Nil       = [| acc <>> pure Nil |]
        go acc (c :: cs) = go ((:<) <$> acc <*> g c) cs

bindString : String -> (Char -> String) -> String
bindString s f = pack $ go Lin $ unpack s
  where go : SnocList Char -> List Char -> List Char
        go acc Nil       = acc <>> Nil
        go acc (c :: cs) = go (acc <>< unpack (f c)) cs

map : (Char -> Char) -> String -> String
map f = pack . map f . unpack

filter : (Char -> Bool) -> String -> String
filter f = pack . filter f . unpack

mapMaybe : (Char -> Maybe Char) -> String -> String
mapMaybe f = pack . mapMaybe f . unpack

foldl : (a -> Char -> a) -> a -> String -> a
foldl f v = foldl f v . unpack

foldMap : Monoid m => (Char -> m) -> String -> m
foldMap f = foldMap f . unpack

traverse : Applicative f => (Char -> f Char) -> String -> f String
traverse fun = map pack . traverse fun . unpack

(>>=) : String -> (Char -> String) -> String
(>>=) = flip foldMap



--  ****** Integers ******



--  *** Integers Literals ***



record Charge where
  constructor MkCharge
  value : Integer

fromInteger : Integer -> Charge
fromInteger = MkCharge

Semigroup Charge where
  x <+> y = MkCharge $ x.value + y.value

Monoid Charge where
  neutral = 0



--  *** Exercises part 2 ***



record And a where
  constructor MkAnd
  value : a

Bits a => Semigroup (And a) where
  x <+> y = MkAnd $ x.value .&. y.value

Bits a => Monoid (And a) where
  neutral = MkAnd oneBits

record Or a where
  constructor MkOr
  value : a

Bits a => Semigroup (Or a) where
  x <+> y = MkOr $ x.value .|. y.value

Bits a => Monoid (Or a) where
  neutral = MkOr zeroBits

even : Bits64 -> Bool
even = not . flip testBit 0

binChar : Bits64 -> Char
binChar b = if testBit b 0 then '1' else '0'

toBin : Bits64 -> String
toBin = pack . go 64 Nil
  where go : Nat -> List Char -> Bits64 -> List Char
        go Z     acc _ = acc
        go (S k) acc b = go k (binChar b :: acc) (b `shiftR` 1)

toHexChar : (a,b,c,d : Bool) -> Char
toHexChar False False False False = '0'
toHexChar False False False True  = '1'
toHexChar False False True  False = '2'
toHexChar False False True  True  = '3'
toHexChar False True  False False = '4'
toHexChar False True  False True  = '5'
toHexChar False True  True  False = '6'
toHexChar False True  True  True  = '7'
toHexChar True  False False False = '8'
toHexChar True  False False True  = '9'
toHexChar True  False True  False = 'a'
toHexChar True  False True  True  = 'b'
toHexChar True  True  False False = 'c'
toHexChar True  True  False True  = 'd'
toHexChar True  True  True  False = 'e'
toHexChar True  True  True  True  = 'f'

hexChar : Bits64 -> Char
hexChar b = toHexChar (testBit b 3) (testBit b 2) (testBit b 1) (testBit b 0)

toHex : Bits64 -> String
toHex = pack . go 64 Nil
  where go : Nat -> List Char -> Bits64 -> List Char
        go Z     acc _ = acc
        go (S k) acc b = go k (hexChar b :: acc) (b `shiftR` 4)



--  ****** Refined Primitives ******



--  *** Use Case: ASCII Strings ***



isAsciiChar : Char -> Bool
isAsciiChar = (<= 127) . ord

isAsciiString : String -> Bool
isAsciiString = all isAsciiChar . unpack

record Ascii where
  constructor MkAscii
  value : String
  0 prf : isAsciiString value === True

hello : Ascii
hello = MkAscii "Hello World!" Refl

fromString : (s : String) -> (prf : isAsciiString s === True) => Ascii
fromString s = MkAscii s prf

hello2 : Ascii
hello2 = "Hello World!"

test : (b : Bool) -> Dec (b === True)
test True  = Yes Refl
test False = No absurd

ascii : String -> Maybe Ascii
ascii x = case test (isAsciiString x) of
  Yes prf   => Just $ MkAscii x prf
  No contra => Nothing

0 allAppend :  (f : Char -> Bool)
            -> (s1,s2 : String)
            -> (p1 : all f (unpack s1) === True)
            -> (p2 : all f (unpack s2) === True)
            -> all f (unpack (s1 ++ s2)) === True
allAppend f s1 s2 p1 p2 = believe_me $ Refl {x = True}

namespace Ascii
  export
  (++) : Ascii -> Ascii -> Ascii
  MkAscii s1 p1 ++ MkAscii s2 p2 =
    MkAscii (s1 ++ s2) $ allAppend isAsciiChar s1 s2 p1 p2



--  *** Use Case: Sanitized HTML ***



escape : String -> String
escape = concat . map esc . unpack
  where esc : Char -> String
        esc '<'  = "&lt;"
        esc '>'  = "&gt;"
        esc '"'  = "&quot;"
        esc '&'  = "&amp;"
        esc '\'' = "&apos;"
        esc c    = singleton c

record Escaped where
  constructor MkEscaped
  value    : String
  0 origin : String
  0 prf    : escape origin === value

namespace Escaped
  export
  fromString : (s : String) -> (prf : escape s === s) => Escaped
  fromString s = MkEscaped s s prf

escaped : Escaped
escaped = "Hello \&quot;World\&quot;!"

