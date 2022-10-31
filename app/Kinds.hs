{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

---------------------------------------
-- Chapter 2: Terms, Types and Kinds --
---------------------------------------

-- 2.1   The Kind System
-- 2.1.1 The Kind of "Types"
-- 2.1.2 Arrow Kinds
-- 2.1.3 Constraint Kinds
-- 2.2   Data Kinds
-- 2.3   Promotion of Built-In Types
-- 2.3.1 Symbols
-- 2.3.2 Natural Numbers
-- 2.3.3 Lists
-- 2.3.4 Tuples
-- 2.4   Type-Level Functions

module Kinds where

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Maybe (fromJust, fromMaybe)
import Data.Proxy
import GHC.TypeLits
import Prelude hiding (Bool (..), map)

-------------------------
-- 2.1 The Kind System --
-------------------------

-- In everyday Haskell programming, the fundamental building blocks are those of TERMS and TYPES.
-- Types are little more than sanity checks: PROOFS to the compiler that the programs make some sense.

-- The fundamental building blocks for type-level programming are TYPES and KINDS.
-- The TYPES now become the things to manipulate, and the KINDS become the PROOFS.

-- Terms are the values you can manipulate - the things that exist at runtime.

-- The kind system can be described as "the type system for types".
-- By that line of reasoning, kinds are "the types of types".

-- >>> :type 5
-- 5 ∷ Num a ⇒ a

-- >>> :kind Num
-- Num ∷ Type → Constraint

-- >>> :type "Chaîne de Caractères"
-- "Chaîne de Caractères" ∷ String

-- >>> :kind String
-- String ∷ Type

-- >>> :kind Int
-- Int ∷ Type

-----------------------
-- 2.1.2 Arrow Kinds --
-----------------------

-- Higher-kinded types (HKTs) are those with type variables.

-- >>> :kind Maybe
-- Maybe ∷ Type → Type

-- >>> :kind Either
-- Either ∷ Type → Type → Type

-- >>> :kind Monad
-- Monad ∷ (Type → Type) → Constraint

-- >>> :kind MaybeT
-- MaybeT ∷ (Type → Type) → Type → Type

----------------------------
-- 2.1.3 Constraint Kinds --
----------------------------

-- >>> :type show
-- show ∷ Show a ⇒ a → String

-- >>> :kind Show
-- Show ∷ Type → Constraint

-- Constraint is the kind of any fully-saturated typeclass!

-- >>> :kind Show Int
-- Show Int ∷ Constraint

-- We have `Type`, `Constraint` and arrow derivatives (→). THAT'S ALL!!!
-- Without further language extensions, this is the extent of the expressiveness of Haskell's kind system.

-- Exercise 2.1.3-i
-- >>> :kind Show
-- Show ∷ Type → Constraint

-- Exercise 2.1.3-ii
-- >>> :kind Functor
-- Functor ∷ (Type → Type) → Constraint

-- Exercise 2.1.3-iii
-- >>> :kind Monad
-- Monad ∷ (Type → Type) → Constraint

-- Exercise 2.1.3-iv
-- >>> :kind MonadTrans
-- MonadTrans ∷ ((Type → Type) → Type → Type) → Constraint

--------------------
-- 2.2 Data Kinds --
--------------------

-- The DataKinds extension lifts data constructors into type constructors and types into kinds!
-- data → type
-- type → kind

data Bool -- type (constructor) of kind Type                                    (1)
  = True --- data (constructor) of type Bool ⇒ exists at runtime                (2)
  | False -- data (constructor) of type Bool ⇒ exists at runtime                (3)

-- With DataKinds the above type definition of Bool also gives us the following kind definition. (This is not legal Haskell syntax.)
-- kind Bool   -- kind (constructor) (doesn't go any higher)                     (4)
--   = 'True   -- type (constructor) of kind Bool (= promoted data constructor)  (5)
--   | 'False  -- type (constructor) of kind Bool (= promoted data constructor)  (6)

-- (1)
-- >>> :kind Bool
-- Bool ∷ Type

-- (2)
-- >>> :type True
-- True ∷ Bool

-- (3)
-- >>> :type False
-- False ∷ Bool

-- (4) cannot be asked for

-- The apostrophes on 'True and 'False are known as TICKS, and are used to distinguish promoted data constructors from everyday type constructors.

-- (5)
-- >>> :kind 'True
-- 'True ∷ Bool

-- (6)
-- >>> :kind 'False
-- 'False ∷ Bool

-- The ticks aren't always necessary.

-- (5)
-- >>> :kind True
-- True ∷ Bool

-- (6)
-- >>> :kind False
-- False ∷ Bool

-- In this example it's very important to differentiate between the type constructor Unit (of kind TYPE),
-- and the promoted data constructor 'Unit - which is a type - of kind UNIT.
data Unit = Unit

-- creates ⇒
-- Unit = type   (1)
-- Unit = data   (2)

-- pseudo-code because of DataKinds
-- kind Unit = 'Unit

-- creates ⇒
-- Unit = kind   (3)
-- 'Unit = type  (4)

-- (1)
-- >>> :kind Unit
-- Unit ∷ Type

-- (2)
-- >>> :type Unit
-- Unit ∷ Unit

-- (3) cannot be asked for

-- (4)
-- >>> :kind 'Unit
-- 'Unit ∷ Unit

-- Maybe accepts only Type
-- >>> :kind Maybe
-- Maybe ∷ Type → Type

-- ✓ (will work with Maybe)
-- >>> :kind Unit
-- Unit ∷ Type

-- ✗ (won't work with Maybe)
-- >>> :kind 'Unit
-- 'Unit ∷ Unit

-- >>> :kind Maybe Unit
-- Maybe Unit ∷ Type

-- We have to be careful what we really mean, Unit or 'Unit.
-- >>> :kind Maybe 'Unit
-- Expected a type, but 'Unit has kind `Unit'

-- Type-level programming in Haskell without DataKinds is equivalent to programming in a dynamically typed language.
-- By default, having every kind you manipulate be Type is a lot like having all of your terms be of the same type.

-- Promoted data constructors can be used as phantom parameters.

-- We can provide a UserType type whose only purpose is to give us access to its promoted data constructors ('RegularUser, 'Admin).
data UserType = RegularUser | Admin

-- >>> :kind 'Admin
-- 'Admin ∷ UserType

-- this won't compile: "Expected a type, but ‘'Admin’ has kind ‘UserType’"
-- newtype User1 = User1 {userAdminToken1 ∷ 'Admin}

-- Proxy takes a type of kind k and returns a Type.
-- >>> :kind Proxy
-- Proxy ∷ k → Type

-- >>> :kind Proxy 'Admin
-- Proxy 'Admin ∷ Type

-- >>> :kind Maybe (Proxy 'Admin)
-- Maybe (Proxy 'Admin) ∷ Type

-- now it works
-- A user has potentially an administration token.
newtype User = User {userAdminToken ∷ Maybe (Proxy 'Admin)}
  deriving (Show)

-- We make sensitive operations require a copy of this administration token.
-- This minor change will cause a type error whenever doSensitiveThings is called without an administration token.
-- TODO: [Doesn't make sense to me!](shorturl.at/JTWX9)
doSensitiveThings ∷ Proxy 'Admin → Int
doSensitiveThings _ = 42

regUser ∷ User
regUser = User Nothing

adminUser ∷ User
adminUser = User (Just Proxy)

-- >>> userAdminToken regUser
-- Nothing

-- What???
-- >>> fromJust $ userAdminToken regUser
-- Proxy

-- >>> :type fromJust $ userAdminToken regUser
-- fromJust $ userAdminToken regUser ∷ Proxy 'Admin

-- >>> userAdminToken adminUser
-- Just Proxy

-- >>> fromJust $ userAdminToken adminUser
-- Proxy

-- >>> doSensitiveThings $ fromJust (userAdminToken regUser)
-- 42

-- >>> doSensitiveThings $ fromJust (userAdminToken adminUser)
-- 42

-- >>> doSensitiveThings Proxy
-- 42

-------------------------------------
-- 2.3 Promotion of Built-In Types --
-------------------------------------

-- With DataKinds enabled almost all types automatically promote to kinds including the built-in ones.
-- Since built-in types (strings, numbers, lists and tuples) have special syntaxes at the term-level,
-- we expect them to behave oddly at the type-level as well.
-- For playing with promoted built-in types need the GHC.TypeLits module.

-------------------
-- 2.3.1 Symbols --
-------------------

-- The promoted version of a String is called a SYMBOL.
-- SYMBOLs are NOT lists of characters.
-- Symbol type literals can be written by just using a string literal in a place where a type is expected!

-- >>> :type "hello"
-- "hello" ∷ String

-- >>> :kind "hello"
-- "hello" ∷ Symbol

-- >>> :kind! UnconsSymbol "hello"
-- UnconsSymbol "hello" ∷ Maybe (Char, Symbol)
-- = 'Just '('h', "ello")

-- >>> :kind! ConsSymbol 'h' "ello"
-- ConsSymbol 'h' "ello" ∷ Symbol
-- = "hello"

-- >>> :kind AppendSymbol
-- AppendSymbol ∷ Symbol → Symbol → Symbol

-- >>> :kind AppendSymbol "thinking" " with types"
-- AppendSymbol "thinking" " with types" ∷ Symbol

-- >>> :kind! AppendSymbol "thinking" " with types"
-- AppendSymbol "thinking" " with types" ∷ Symbol
-- = "thinking with types"

-- Additionally, we are capable of comparing SYMBOLs via the CmpSymbol primitive.

-- Note: `Ordering` is the DataKinds promoted version of the standard Ordering type!
-- >>> :kind CmpSymbol
-- CmpSymbol ∷ Symbol → Symbol → Ordering

-- >>> :kind CmpSymbol "Michael" "Michael"
-- CmpSymbol "Michael" "Michael" ∷ Ordering

-- >>> :kind! CmpSymbol "Michael" "Michael"
-- CmpSymbol "Michael" "Michael" ∷ Ordering
-- = 'EQ

-- >>> :kind! CmpSymbol "Michael" "Kohlhaas"
-- CmpSymbol "Michael" "Kohlhaas" ∷ Ordering
-- = 'GT

---------------------------
-- 2.3.2 Natural Numbers --
---------------------------

-- Promotion of numbers:
-- Only the natural numbers (0, 1, 2, . . .) can be promoted.
-- These natural numbers are of kind Natural.

-- >>> :type 5
-- 5 ∷ Num a ⇒ a

-- >>> :kind 5
-- 5 ∷ Natural

-- >>> :kind! 5
-- 5 ∷ Natural
-- = 5

-- performing arithmetic on NATs - addition, subtraction, multiplication, exponentiation, log, ...
-- >>> :kind! ((1 + 17) * 3) `Div ` 8
-- ((1 + 17) * 3) `Div ` 8 ∷ Natural
-- = 6

-- >>> :kind! 2 ^ 3
-- 2 ^ 3 ∷ Natural
-- = 8

-----------------
-- 2.3.3 Lists --
-----------------

-- If lists were defined as library code, without any special syntax, they'd have the following definition:
-- (Because lists' data constructors have symbolic names, they also require TypeOperators enabled.)
-- data [a] = [] | a : [a]

-- This is exactly what the promoted data constructors of lists look like:
-- list of kinds
-- >>> :kind! '[]
-- '[] ∷ [a]
-- = '[]

-- >>> :kind! '[Int]
-- '[Int] ∷ [Type]
-- = '[Int]

-- >>> :kind! '[Int, Int]
-- '[Int, Int] ∷ [Type]
-- = '[Int, Int]

-- heterogenous lists are not allowed
-- >>> :kind! '[Show, Int]
-- Expected kind `Type → Constraint', but `Int' has kind `Type'
-- In the type '[Show, Int]

-- this is NOT a heterogenous list
-- >>> :kind! '[Maybe Int, Int]
-- '[Maybe Int, Int] ∷ [Type]
-- = '[Maybe Int, Int]

-- this is NOT a heterogenous list
-- >>> :kind! '[Maybe Int, Either Int String]
-- '[Maybe Int, Either Int String] ∷ [Type]
-- = '[Maybe Int, Either Int [Char]]

-- >>> :kind! '[Maybe, Either Int]
-- '[Maybe, Either Int] ∷ [Type → Type]
-- = '[Maybe, Either Int]

-- >>> :kind! '[Unit]
-- '[Unit] ∷ [Type]
-- = '[Unit]

-- >>> :kind! '[ 'Unit]
-- '[ 'Unit] ∷ [Unit]
-- = '[ 'Unit]

-- >>> :kind! '["hello"]
-- '["hello"] ∷ [Symbol]
-- = '["hello"]

-- >>> :kind! '(:)
-- '(:) ∷ a → [a] → [a]
-- = (':)

-- >>> :kind! Maybe Int
-- Maybe Int ∷ Type
-- = Maybe Int

-- >>> :kind! "hello"
-- "hello" ∷ Symbol
-- = "hello"

-- >>> :kind! '[Int]
-- '[Int] ∷ [Type]
-- = '[Int]

-- >>> :kind! Maybe Int ': '[Int]
-- Maybe Int ': '[Int] ∷ [Type]
-- = '[Maybe Int, Int]

-- >>> :kind! "hello" ': '[Int]
-- Couldn't match kind `Type' with `Symbol'
-- Expected kind `[Symbol]', but '[Int] has kind `[Type]'
-- In the second argument of `(:)', namely '[Int]
-- In the type `"hello" : '[Int]'

-- [Bool] is of kind Type and describes a term-level list of booleans.
-- The type '[Bool] is of kind [Type] and describes a type-level list with ONE(!) element (namely, the type Bool.)

-- >>> :kind [Bool]
-- [Bool] ∷ Type

-- >>> :kind '[Bool]
-- '[Bool] ∷ [Type]

-- >>> :kind '[Bool, Int]
-- '[Bool, Int] ∷ [Type]

-- Due to the way GHC's lexer parses character literals ('a'), make sure you add a space after starting a promoted list.
-- "'['" results in a parsing error.

-- '[' not allowed
-- >>> :kind '['True ]
-- parse error on input `]'

-- needs a space
-- >>> :kind '[ 'True ]
-- '[ 'True ] ∷ [Bool]

------------------
-- 2.3.4 Tuples --
------------------

-- Tuples promote straightforwardly via the '(,) constructor.
-- As expected tuples are promoted with a leading tick.

-- >>> :kind '(2 , "tuple")
-- '(2 , "tuple") ∷ (Natural, Symbol)

-- >>> :kind '(2 , "tuple", 'c')
-- '(2 , "tuple", 'c') ∷ (Natural, Symbol, Char)

------------------------------
-- 2.4 Type-Level Functions --
------------------------------

-- Where DataKinds really begins to shine is through the introduction of CLOSED TYPE FAMILIES.
-- You can think of closed type families as functions at the type-level.
-- CmpSymbol, Div, ... from above are all closed type families.

-- [Type Families in Haskell: The Definitive Guide](https://serokell.io/blog/type-families-haskell)

-- No way to automagically promote term-level functions into type-level ones (like data constructors).
-- You can think of closed type families as functions at the type-level!
-- Type families are like functions for types and need extension TypeFamilies.

-- regular term-level function
or ∷ Bool → Bool → Bool -- type signature
or True _ = True
or False y = y

-- The closed type family `Or` requires a capital letter for the beginning of its name, because it exists at the type-level.
-- type family Or (x ∷ Bool) (y ∷ Bool) ∷ Bool where
--   Or 'True _ = 'True
--   Or 'False y = y

-- alternative syntax
-- type family version of `or`
type Or ∷ Bool → Bool → Bool -- kind signature!!!
type family Or x y where
  Or 'True _ = 'True
  Or 'False y = y

-- >>> :kind! Or 'True
-- Or 'True ∷ Bool → Bool
-- = Or 'True

-- >>> :kind! Or 'True 'False
-- Or 'True 'False ∷ Bool
-- = 'True

-- >>> :kind! Or 'False 'False
-- Or 'False 'False ∷ Bool
-- = 'False

type And ∷ Bool → Bool → Bool
type family And x y where
  And 'True y = y
  And 'False y = 'False

-- >>> :kind! And 'True
-- And 'True ∷ Bool → Bool
-- = And 'True

-- >>> :kind! And 'True 'False
-- And 'True 'False ∷ Bool
-- = 'False

-- >>> :kind! And 'False 'False
-- And 'False 'False ∷ Bool
-- = 'False

-- >>> :kind! And 'True 'True
-- And 'True 'True ∷ Bool
-- = 'True

--------------------
-- Exercise 2.4-i --
--------------------

-- regular version
not ∷ Bool → Bool
not True = False
not False = True

type Not ∷ Bool → Bool
type family Not x where
  Not 'True = 'False
  Not 'False = 'True

-- >>> :kind! Not 'True
-- Not 'True ∷ Bool
-- = 'False

-- >>> :kind! Not 'False
-- Not 'False ∷ Bool
-- = 'True

-- While the metaphor between type families and functions is enticing, it isn't entirely correct.
-- The analogues break down in several ways, but the most important one is that type families must be SATURATED (???).
-- Another way of saying this is that all of a type family's parameters must be specified simultaneously.
-- There is NO CURRYING available.

-- regular map function
map ∷ (a → b) → [a] → [b]
map _ [] = []
map f (a : as) = f a : map f as

-- promoting map to the type level
type Map ∷ (a → b) → [a] → [b]
type family Map f xs where
  Map _ '[] = '[]
  Map f (a : as) = f a : Map f as

-- >>> :kind! Maybe
-- Maybe ∷ Type → Type
-- = Maybe

-- Maybe works ...
-- >>> :kind! Map Maybe
-- Map Maybe ∷ [Type] → [Type]
-- = Map Maybe

-- ... but Or - as it is a type family - doesn't as it must be saturated.
-- >>> :kind! Map (Or 'True)
-- The type family `Or' should have 2 arguments, but has been given 1

-- Maybe works ...
-- >>> :kind! Map Maybe '[Int, String]
-- Map Maybe '[Int, String] ∷ [Type]
-- = '[Maybe Int, Maybe [Char]]

-- ... but Map doesn't.
-- >>> :type undefined ∷ Proxy (Map (Or 'True))
-- The type family `Map' should have 2 arguments, but has been given 1
-- In an expression type signature: Proxy (Map (Or 'True))
-- In the expression: undefined ∷ Proxy (Map (Or 'True))

-- Because we're unable to partially apply closed type families, Map doesn't turn out to be very useful.

-- >>> :type undefined ∷ Proxy (Or 'True)
-- The type family `Or' should have 2 arguments, but has been given 1
-- In an expression type signature: Proxy (Or 'True)
-- In the expression: undefined ∷ Proxy (Or 'True)

-- Type families also have a kind.

-- The kind you write after the `∷` is the kind of the type returned by the type family, not the kind of the type family itself.
type Foo ∷ Bool → Bool → Bool
type family Foo x y

type family Bar x y ∷ Bool → Bool → Bool

-- >>> :kind Foo
-- Foo ∷ Bool → Bool → Bool

-- >>> :kind Bar
-- Bar ∷ Type → Type → Bool → Bool → Bool
