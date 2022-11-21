{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

-----------------------------------------
-- Chapter 1: The Algebra Behind Types --
-----------------------------------------

-- 1.1 Isomorphisms and Cardinalities
-- 1.2 Sum, Product and Exponential Types
-- 1.3 Example: Tic-Tac-Toe
-- 1.4 The Curry–Howard Isomorphism
-- 1.5 Canonical Representations

module Algebra where

import Control.Monad (guard, join)
import Data.Maybe (isJust, listToMaybe)
import Data.Void (Void, absurd)
import Data.Word (Word8)

----------------------------------------
-- 1.1 Isomorphisms and Cardinalities --
----------------------------------------

{-

-- Cardinality ("number of inhabitants")

-- Cardinality = 0
data Void

-- Unit
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

--  |Maybe a| = 1 + |a|

-}

data Spin = Up | Down

-- Spin ≅ Bool
-- We have two isomorphisms:
-- In general, for any two types with cardinality n, there are n! unique isomorphisms between them.

-- As far as the math goes, any of these is just as good as any other.
-- And for most purposes, knowing that an isomorphism exists is enough.

-- An isomorphism between types `s` and `t` is a proof that for all intents and purposes, `s` and `t` are the same thing.
-- Any two types with the same cardinality are isomorphic!

--  |Bool| = 2 ⇒ 2! = 2 isomorphisms

-- >>> :type (spinToBool1 . boolToSpin1)
-- (spinToBool1 . boolToSpin1) :: Bool -> Bool

-- >>> :type (boolToSpin1 . spinToBool1)
-- (boolToSpin1 . spinToBool1) :: Spin -> Spin

-- >>> :type (spinToBool2 . boolToSpin2)
-- (spinToBool2 . boolToSpin2) :: Bool -> Bool

-- >>> :type (boolToSpin2 . spinToBool2)
-- (boolToSpin2 . spinToBool2) :: Spin -> Spin

-- 1st isomorphism
spinToBool1 ∷ Spin → Bool
spinToBool1 Up = False
spinToBool1 Down = True

boolToSpin1 ∷ Bool → Spin
boolToSpin1 False = Up
boolToSpin1 True = Down

-- 2nd isomorphism
spinToBool2 ∷ Spin → Bool
spinToBool2 Up = True
spinToBool2 Down = False

boolToSpin2 ∷ Bool → Spin
boolToSpin2 False = Down
boolToSpin2 True = Up

--------------------------------------------
-- 1.2 Sum, Product and Exponential Types --
--------------------------------------------

-- sum types ("Addition")
data Deal a b
  = This !a
  | That !b
  | TheOther !Bool

--  |Deal a b| = |a| + |b| + |Bool|
--             = |a| + |b| + 2

--  |Maybe a| = 1 + |a|

-- Pair is a product type ("Multiplication")

--  |(a, b)| = |a| × |b|

-- MixedFraction is a product type
data MixedFraction a = Fraction
  { mixedBit ∷ !Word8,
    numerator ∷ !a,
    denominator ∷ !a
  }

--  |MixedFraction a| = |Word8| × |a| × |a| = 256 × |a| × |a|

-- We can express mathematical truths in terms of types.
-- We can prove that `a × 1 = a` by showing an isomorphism between `(a, ())` and `a`.

-- We can think of the Unit type as being a MONOIDAL IDENTITY for product types:
prodUnitTo ∷ a → (a, ())
prodUnitTo a = (a, ())

prodUnitFrom ∷ (a, ()) → a
prodUnitFrom (a, ()) = a

-- >>> :type prodUnitFrom . prodUnitTo
-- prodUnitFrom . prodUnitTo :: c -> c

-- >>> :type prodUnitTo . prodUnitFrom
-- prodUnitTo . prodUnitFrom :: (b, ()) -> (b, ())

-- We can prove that `a + 0 = a` by showing an isomorphism between e.g. `Either a Void` and `a`.

-- `Either a b` is a sum type: |Either a b| = |a| + |b|

-- Void acts as a MONOIDAL UNIT for sum types.

-- The function `absurd` has the type `Void → a`.
-- It's a sort of bluff saying "if you give me a Void I can give you anything you want."
-- This is a promise that can never be fulfilled, but because there are no Voids to be had in the first place, we can't disprove such a claim.

sumUnitTo ∷ Either a Void → a
sumUnitTo (Left a) = a
sumUnitTo (Right v) = absurd v

sumUnitFrom ∷ a → Either a Void
sumUnitFrom = Left

-- >>> :type sumUnitFrom . sumUnitTo
-- sumUnitFrom . sumUnitTo :: Either b Void -> Either b Void

-- >>> :type sumUnitTo . sumUnitFrom
-- sumUnitTo . sumUnitFrom :: c -> c

-- Function types also have an encoding as statements about cardinality. They correspond to exponentialization.
-- E.g, there are exactly four (2^2) inhabitants of the type `Bool → Bool`.
-- These functions are `id`, `not`, `const True` and `const False`.

-- More generally, the type `a → b` has cardinality `|b| ^ |a|`.
-- While this might be surprising at first. It always seems backwards to me. But the argument is straightforward.
-- For every value of `a` in the domain, we need to give back a `b`. But we can chose any value of `b` for every value of `a`, resulting in the following equality:

--  |a → b| = |b| × |b| × · · · × |b| = |b| ^ |a|

-- e.g.

--  |a → b| ⇒ |b| ^ |a| = 3 ^ 2 = 9
--  a ∈ a, b    ⇒ |a| = 2
--  b ∈ A, B, C ⇒ |b| = 3
--
--    | a | b
--  ==========
--  1 | A | A
--  2 | A | B
--  3 | A | C
--  4 | B | A
--  5 | B | B
--  6 | B | C
--  7 | C | A
--  8 | C | B
--  9 | C | C
--
--  |a → b| ⇒ |b| ^ |a| = 2 ^ 3 = 8
--  a ∈ a, b, c ⇒ |a| = 3
--  b ∈ A, B    ⇒ |b| = 2
--
--    | a | b | c
--  ==============
--  1 | A | A | A
--  2 | A | A | B
--  3 | A | B | A
--  4 | A | B | B
--  5 | B | A | A
--  6 | B | A | B
--  7 | B | B | A
--  8 | B | B | B

-- Cookbook recipe:
-- • Addition ≈ Either a b
-- • Multiplication ≈ (,)
-- • Exponantation ≈ function: |a → b| ≅ |b| ^ |a|
-- • 0 ≈ Void
-- • 1 ≈ Unit
-- • Prove algebraic equation by proving isomorphism:
--   1. from . to = id
--   2. to . from = id

------------------------------
-- 1.3 Example: Tic-Tac-Toe --
------------------------------

-- naive implementation of TicTacToe
data TicTacToe a = TicTacToe
  { topLeft ∷ !a,
    topCenter ∷ !a,
    topRight ∷ !a,
    midLeft ∷ !a,
    midCenter ∷ !a,
    midRight ∷ !a,
    botLeft ∷ !a,
    botCenter ∷ !a,
    botRight ∷ !a
  }

data Player = X | O
  deriving (Eq, Show)

{- ORMOLU_DISABLE -}

-- unwieldy
emptyBoard1 ∷ TicTacToe (Maybe Player)
emptyBoard1 =
  TicTacToe
    Nothing Nothing Nothing
    Nothing Nothing Nothing
    Nothing Nothing Nothing

board1 ∷ TicTacToe (Maybe Player)
board1 =
  TicTacToe
    (Just X) Nothing  Nothing
    Nothing  (Just X) Nothing
    Nothing  Nothing  (Just X)

board2 ∷ TicTacToe (Maybe Player)
board2 =
  TicTacToe
    Nothing (Just O) Nothing
    Nothing (Just O) Nothing
    Nothing (Just O) Nothing

board3 ∷ TicTacToe (Maybe Player)
board3 =
  TicTacToe
    (Just X) (Just O) (Just O)
    (Just O) (Just O) (Just X)
    (Just X) (Just X) (Just O)

{- ORMOLU_ENABLE -}

-- functions are even more convoluted
checkWinner ∷ TicTacToe (Maybe Player) → Maybe Player
checkWinner TicTacToe {..} = join $
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
    guard $ isJust one && (two == one) && (three == one)
    pure one

-- >>> checkWinner emptyBoard1
-- Nothing

-- >>> checkWinner board1
-- Just X

-- >>> checkWinner board2
-- Just O

-- >>> checkWinner board3
-- Nothing

--  |TicTacToe a| = |a| × |a| × · · · × |a|
--                = |a| ^ (3×3)
--                = |a| ^ 9

-- We see that TicTacToe is isomorphic to a function `(Three, Three) → a`,
-- or in its curried form: `Three → Three → a`.
-- Of course, Three is any type with three inhabitants:
data Three = One | Two | Three
  deriving (Eq, Ord, Enum, Bounded)

-- corresponds to the coordinate system of TicTacToe

{- ORMOLU_DISABLE -}

--  ------------------------------------------
--  |  One,  One |  One,  Two |  One,  Three |
--  ------------------------------------------
--  |  Two,  One |  Two,  Two |  Two,  Three |
--  ------------------------------------------
--  | Three, One | Three, Two | Three, Three |
--  ------------------------------------------

{- ORMOLU_ENABLE -}

newtype TicTacToe2 a = TicTacToe2 {board ∷ Three → Three → a}

-- smarter implementation of an empty board
emptyBoard2 ∷ TicTacToe2 (Maybe Bool)
emptyBoard2 = TicTacToe2 (\_ _ → Nothing)

-- Making this change, we are rewarded with the entire toolbox of combinators for working with functions.
-- We gain better compositionality and have to pay less of a cognitive burden.

--------------------------------------
-- 1.4 The Curry–Howard Isomorphism --
--------------------------------------

-- Curry-Howard isomorphism:
-- Every statement in logic is equivalent to some computer program, and vice versa, i.e. an isomorphism between logic and computer program.
-- There is no essential distinction between having a value and having a (pure) program that computes that value.

-- Curry-Howard isomorphism is a profound insight about our universe.
-- It allows us to analyze mathematical theorems through the lens of functional programming.

-- Algebra | Logic  |   Types
-- ===============================
--  a + b  | a ∨ b  | Either a b
--  a × b  | a ∧ b  |  (a, b)
--  b ^ a  | a ⇒ b  |  a → b
--  a = b  | a ⇔ b  | isomorphism
--    0    |   ⊥    |   Void
--    1    |   ⊤    |    ()

-----------------------------------
-- 1.5 Canonical Representations --
-----------------------------------

-- It's often useful to have a conventional form when working with types generically.
-- This CANONICAL REPRESENTATION is known as a sum of products, and refers to any type t of the form,

-- t = ∑ ∏ tm,n
--     m n

-- Essentially it means "addition (sum type) on the outside and "multiplication" (product type) on the inside".

-- Canonically represented:
-- ()
-- Either a b
-- Either (a, b) (c, d)
-- Either a (Either b (c, d))
-- a → b
-- (a, b)
-- (a, Int) -- Int is not a sum type (we make an exception to the rule for numeric types as it would be too much work to express them as sums)

-- NOT canonically represented:
-- (a, Either b c) -- sum type `Either b c` is inside ⇒ not a canonical reprentation
-- (a, Bool)       -- sum type    `Bool`    is inside ⇒ not a canonical reprentation

-- The canonical representation of `Maybe a` is `Either a ()`.

---------------
-- Exercises --
---------------

-- Exercise 1.2-i
-- Either Bool (Bool, Maybe Bool) → Bool

-- Either Bool (Bool, Maybe Bool) → Bool
--        |2 |  |2 |  |   3    |    |2 |
--        |2 | |   2 × 3 = 6    |   |2 |

-- |         2 + 6 = 8          |   |2 |
--                          2 ^ 8 = 256

-- Exercise 1.4-i
-- Algebraic equation to types: (a^b)^c ≡ (b → a)^c ≡ c → (b → a) ≡ c → b → a -- function application is right associative
-- Algebraic equation to types: (a^(b×c) ≡ (b×c) → a ≡ (b,c) → a
-- Isomorphism: 1. (c → b → a) → (b, c) → a
--              2. ((b,c) → a) → c → b → a

to1 ∷ (c → b → a) → (b, c) → a
to1 f (b, c) = f c b

from1 ∷ ((b, c) → a) → c → b → a
from1 f c b = f (b, c)

-- from1 . to1 = id
-- to1 . from1 = id

-- If you swap b and c for the multiplication in 1. and 2. you get:
to2 ∷ (c → b → a) → (c, b) → a
to2 f (c, b) = f c b

from2 ∷ ((c, b) → a) → c → b → a
from2 f c b = f (c, b)

-- from2 . to2 = id
-- to2 . from2 = id

-- Swapping parameter names (a ↔ c) results in the well-known functions curry and uncurry:
-- uncurry
to3 ∷ (a → b → c) → (a, b) → c
to3 f (a, b) = f a b

-- curry
from3 ∷ ((a, b) → c) → a → b → c
from3 f a b = f (a, b)

-- from3 . to3 = id
-- to3 . from3 = id

-- Exercise 1.4-ii
-- a^b × a^c = a^(b+c)
-- (b → a, c → a) = Either b c → a

to4 ∷ (b → a, c → a) → Either b c → a
to4 (f, _) (Left b) = f b
to4 (_, f) (Right c) = f c

from4 ∷ (Either b c → a) → (b → a, c → a)
from4 f = (f . Left, f . Right)

-- from4 . to4 = id
-- to4 . from4 = id

-- Exercise 1.4-iii

-- (a×b)^c = a^c × b^c
-- c → (a, b) = (c → a, c → b)

to5 ∷ (c → (a, b)) → (c → a, c → b)
to5 f = (fst . f, snd . f)

from5 ∷ (c → a, c → b) → c → (a, b)
from5 (f, g) c = (f c, g c)

-- from5 . to5 = id
-- to5 . from5 = id
