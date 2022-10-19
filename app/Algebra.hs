{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Algebra where

import Control.Monad (guard, join)
import Data.Maybe (isJust, listToMaybe)
import Data.Void (Void, absurd)
import Data.Word (Word8)

{-

-- Cardinality ("number of inhabitants")

-- Cardinality = 0
data Void

-- # Unit
-- Cardinality = 1
data () = ()

-- Cardinality = 2
data Bool = False | True

-- |Void| = 0
-- |()|   = 1
-- |Bool| = 2

-- Any two finite types that have the same cardinality will always be isomorphic to one another.
-- An isomorphism between types `s` and `t` is defined as a pair of functions `to` and `from`:

to ∷ s → t
from ∷ t → s

-- In other words: s ≅ t
-- to . from = id
-- from . to = id

-- Where does such a mapping come from?
-- Pick an arbitrary ordering on each type - not necessarily corresponding to an Ord instance - and then
-- map the first element under one ordering to the first element under the other. And so on ...

data Maybe a
  = Nothing
  | Just a

voidUnit ∷ () → (Void → a)
voidUnit _ = absurd

-}

data Spin = Up | Down

-- Spin ≅ Bool
-- We have two isomorphisms:
-- In general, for any two types with cardinality n, there are n! unique isomorphisms between them.

-- As far as the math goes, any of these is just as good as any other.
-- And for most purposes, knowing that an isomorphism exists is enough.

-- An isomorphism between types `s` and `t` is a proof that for all intents and purposes, `s` and `t` are the same thing.
-- Any two types with the same cardinality are isomorphic!

spinToBool1 ∷ Spin → Bool
spinToBool1 Up = False
spinToBool1 Down = True

boolToSpin1 ∷ Bool → Spin
boolToSpin1 False = Up
boolToSpin1 True = Down

spinToBool2 ∷ Spin → Bool
spinToBool2 Up = True
spinToBool2 Down = False

boolToSpin2 ∷ Bool → Spin
boolToSpin2 False = Down
boolToSpin2 True = Up

-- sum types ("Addition")
data Deal a b
  = This a
  | That b
  | TheOther Bool

-- |Deal a b| = |a| + |b| + |Bool|
--            = |a| + |b| + 2

-- |Maybe a| = 1 + |a|

-- Pair is a product type ("Multiplication")

-- |(a, b)| = |a| × |b|

-- MixedFraction is a product type
data MixedFraction a = Fraction
  { mixedBit ∷ Word8,
    numerator ∷ a,
    denominator ∷ a
  }

-- MixedFraction a| = |Word8| × |a| × |a| = 256 × |a| × |a|

-- We can express mathematical truths in terms of types.
-- We can prove that `a × 1 = a` by showing an isomorphism between `(a, ())` and `a`.

-- We can think of the unit type as being a monoidal identity for product types:
prodUnitTo ∷ a → (a, ())
prodUnitTo a = (a, ())

prodUnitFrom ∷ (a, ()) → a
prodUnitFrom (a, ()) = a

-- We can prove that `a + 0 = a` by showing an isomorphism between e.g. `Either a Void` and `a`.

-- Either a b is a sum type:
-- | Either a b| = |a| + |b|

-- Void acts as a monoidal unit for sum types.

-- The function `absurd` at 1 has the type `Void → a`.
-- It's a sort of bluff saying "if you give me a Void I can give you anything you want."
-- This is a promise that can never be fulfilled, but because there are no Voids to be had in the first place, we can't disprove such a claim.

sumUnitTo ∷ Either a Void → a
sumUnitTo (Left a) = a
sumUnitTo (Right v) = absurd v

sumUnitFrom ∷ a → Either a Void
sumUnitFrom = Left

-- Function types also have an encoding as statements about cardinality. They correspond to exponentialization.
-- E.g, there are exactly four (2^2) inhabitants of the type `Bool → Bool`.
-- These functions are `id`, `not`, `const True` and `const False`.

-- More generally, the type a → b has cardinality |b|^|a|.
-- While this might be surprising at first. It always seems backwards to me. But the argument is straightforward.
-- For every value of `a` in the domain, we need to give back a `b`. But we can chose any value of `b` for every value of `a`, resulting in the following equality:

-- |a → b| = |b| × |b| × · · · × |b| = |b|^|a|

-- e.g.
-- a, b → A, B, C
-- 3 ^ 2 = 9
--
--   | a | b
-- ==========
-- 1 | A | A
-- 2 | A | B
-- 3 | A | C
-- 4 | B | A
-- 5 | B | B
-- 6 | B | C
-- 7 | C | A
-- 8 | C | B
-- 9 | C | C
--
-- a, b, c → A, B
-- 2 ^ 3 = 8
--
--   | a | b | c
-- ==============
-- 1 | A | A | A
-- 2 | A | A | B
-- 3 | A | B | A
-- 4 | A | B | B
-- 5 | B | A | A
-- 6 | B | A | B
-- 7 | B | B | A
-- 8 | B | B | B

-- Cookbook:
-- Either a b = addition.
-- (,) = multiplication.
-- function = exponantation: |a → b| ≅ |b|^|a|
-- Void = 0.
-- Unit = 1.
-- Then prove isomorphism to prove algebraic equation.

-- naive implementation of TicTacToe
data TicTacToe a = TicTacToe
  { topLeft ∷ a,
    topCenter ∷ a,
    topRight ∷ a,
    midLeft ∷ a,
    midCenter ∷ a,
    midRight ∷ a,
    botLeft ∷ a,
    botCenter ∷ a,
    botRight ∷ a
  }

{- ORMOLU_DISABLE -}

-- works but pretty unwieldy
emptyBoard ∷ TicTacToe (Maybe Bool)
emptyBoard =
  TicTacToe
    Nothing Nothing Nothing
    Nothing Nothing Nothing
    Nothing Nothing Nothing

{- ORMOLU_ENABLE -}

-- writing functions turn out to be even more involved
checkWinner ∷ TicTacToe (Maybe Bool) → Maybe Bool
checkWinner (TicTacToe {..}) = join $
  listToMaybe $ do
    line ←
      [ [topLeft, topCenter, topRight],
        [midLeft, midCenter, midRight],
        [botLeft, botCenter, botRight],
        [topLeft, midLeft, botLeft],
        [topCenter, midCenter, botCenter],
        [topRight, midRight, botRight],
        [topLeft, midCenter, botRight],
        [topRight, midCenter, botLeft]
        ]
    let [one, two, three] = line
    guard $ isJust one && two == one && three == one
    pure one

-- |TicTacToe a| = |a| × |a| × · · · × |a|
--               = |a| ^ (3×3)
--               = |a| ^ 9

-- We see that TicTacToe is isomorphic to a function `(Three, Three) → a`,
-- or in its curried form: `Three → Three → a`.
-- Of course, Three is any type with three inhabitants:
data Three = One | Two | Three
  deriving (Eq, Ord, Enum, Bounded)

-- like the coordinate system of TicTacToe
-- |  One,  One  |  One,  Two  |  One,  Three
-- |  Two,  One  |  Two,  Two  |  Two,  Three
-- | Three, One  | Three, Two  | Three, Three

newtype TicTacToe2 a = TicTacToe2 {board ∷ Three → Three → a}

-- elegant implementation of emptyBoard
emptyBoard2 ∷ TicTacToe2 (Maybe Bool)
emptyBoard2 = TicTacToe2 $ const $ const Nothing

-- Making this change, we are rewarded with the entire toolbox of combinators for working with functions.
-- We gain better compositionality and have to pay less of a cognitive burden.

-------------
-- Summary --
-------------

-- Curry-Howard isomorphism:
-- Every statement in logic is equivalent to some computer program, and vice versa.
-- There is no essential distinction between having a value and having a (pure) program that computes that value.

-- Algebra | Logic  |   Types
-- ===============================
--  a + b  | a ∨ b  | Either a b
--  a × b  | a ∧ b  |  (a, b)
--  b ^ a  | a ⇒ b  |  a → b
--  a = b  | a ⇔ b  | isomorphism
--    0    |   ⊥    |   Void
--    1    |   ⊤    |    ()

-- It's often useful to have a conventional form when working with types generically.
-- This canonical representation is known as a sum of products, and refers to any type t of the form,

-- t = ∑ ∏ tm,n
--     m n

-- Essentially it means "addition on the outside and multiplication on the inside".

-- canonically represented:
-- ()
-- Either a b
-- Either (a, b) (c, d)
-- Either a (Either b (c, d))
-- a → b
-- (a, b)
-- (a, Int) -- Int is not a sum type (we make an exception to the rule for numeric types as it would be too much work to express them as sums)

-- NOT canonically represented:
-- (a, Either b c)
-- (a, Bool) -- Bool is a sum type

-- The canonical representation of `Maybe a` is `Either a ()`.

---------------
-- Exercises --
---------------

-- Exercise 1.2-i
-- Either Bool (Bool, Maybe Bool) → Bool

-- Either Bool (Bool, Maybe Bool) → Bool
--         2     2        3           2
--         2       2×3=6              2
--           2+6=8                    2
--                              2^8=256

-- Exercise 1.4-i
-- Algebraic equation to types: (a^b)^c ≡ (b → a)^c ≡ c → (b → a) ≡ c → b → a -- function application is right associative
-- Algebraic equation to types: (a^(b×c) ≡ (b×c) → a ≡ (b,c) → a
-- Isomorphism: 1. (c → b → a) → (b,c) → a
--              2. ((b,c) → a) → c → b → a

-- 1. (c → b → a) → (b,c) → a
to1 ∷ (c → b → a) → (b,c) → a
to1 f (b,c) = f c b

-- 2. ((b,c) → a) → (c → b → a)
from1 ∷ ((b,c) → a) → c → b → a
from1 f c b = f (b,c)

-- from1 . to1 = id
-- to1 . from1 = id

-- If you swap b and c for the multiplication in 1. and 2. you get:
to2 ∷ (c → b → a) → (c,b) → a
to2 f (c,b) = f c b

from2 ∷ ((c,b) → a) → c → b → a
from2 f c b = f (c,b)

-- from2 . to2 = id
-- to2 . from2 = id

-- Swapping parameter names (a ↔ c) results in the well-known functions curry and uncurry:
-- uncurry
to3 ∷ (a → b → c) → (a,b) → c
to3 f (a,b) = f a b

-- curry
from3 ∷ ((a,b) → c) → a → b → c
from3 f a b = f (a,b)

-- from3 . to3 = id
-- to3 . from3 = id

-- Exercise 1.4-ii
-- a^b × a^c = a^(b+c)
-- (b → a, c → a) = Either b c → a

-- 1. (b → a, c → a) → Either b c → a
to4 ∷ (b → a, c → a) → Either b c → a
to4 (f, _) (Left b) = f b
to4 (_, f) (Right c) = f c

-- 2. (Either b c → a) → (b → a, c → a)
from4 ∷ (Either b c → a) → (b → a, c → a)
from4 f = (f . Left, f . Right)

-- from4 . to4 = id
-- to4 . from4 = id

-- Exercise 1.4-iii

-- (a×b)^c = a^c × b^c
-- c → (a, b) = (c → a, c → b)

-- 1. (c → (a, b)) → (c → a, c → b)
to5 ∷ (c → (a, b)) → (c → a, c → b)
to5 f = (fst . f, snd . f)

-- 2. (c → a, c → b) → c → (a, b)
from5 ∷ (c → a, c → b) → c → (a, b)
from5 (f, g) c = (f c, g c)

-- from5 . to5 = id
-- to5 . from5 = id

