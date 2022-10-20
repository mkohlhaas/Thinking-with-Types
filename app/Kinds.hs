{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- In everyday Haskell programming, the fundamental building blocks are those of TERMS and TYPES.
-- Types are little more than sanity checks: PROOFS to the compiler that the programs make some sense.

-- The fundamental building blocks for type-level programming are TYPES and KINDS.
-- The TYPES now become the things to manipulate, and the KINDS become the PROOFS.

-- Terms are the values you can manipulate. The things that exist at runtime.

module Kinds where

-- # typelits

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Proxy
import GHC.TypeLits
import Prelude hiding (Bool (..), map)

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

-- >>> :kind Maybe
-- Maybe ∷ Type → Type

-- >>> :kind Either
-- Either ∷ Type → Type → Type

-- >>> :kind Monad
-- Monad ∷ (Type → Type) → Constraint

-- >>> :kind MaybeT
-- MaybeT ∷ (Type → Type) → Type → Type

-- >>> :type show
-- show ∷ Show a ⇒ a → String

-- >>> :kind Show
-- Show ∷ Type → Constraint

-- Without further language extensions, this is the extent of the expressiveness of Haskell's kind system.
-- We have `Type`, `Constraint` and arrow derivatives; that's it!

-- DataKinds lifts data constructors into type constructors and types into kinds!
-- data → type
-- type → kind

data Bool = True | False

-- This creates:
-- a type constructor Bool of kind Type
-- a data constructor True of type Bool
-- a data constructor False of type Bool

-- >>> :kind Bool
-- Bool ∷ Type

-- >>> :type True
-- True ∷ Bool

-- >>> :type False
-- False ∷ Bool

-- With DataKinds the above type definition of Bool also gives us the following kind definition.
-- kind Bool -- this is not legal Haskell syntax
--   = 'True
--   | 'False

-- this creates:
-- a new kind BOOL
-- a promoted data constructor 'True of kind BOOL
-- a promoted data constructor 'False of kind BOOL

-- 'True and 'False are promoted data constructors.

-- The apostrophes on 'True and 'False are known as ticks, and are used to distinguish promoted data constructors from everyday type constructors.

-- >>> :kind 'True
-- 'True ∷ Bool

-- >>> :kind 'False
-- 'False ∷ Bool

-- The ticks aren't always necessary.

-- >>> :kind True
-- True ∷ Bool

-- >>> :kind False
-- False ∷ Bool

-- In this example it's very important to differentiate between the type constructor Unit (of kind TYPE),
-- and the promoted data constructor 'Unit (of kind UNIT.)
data Unit = Unit

-- >>> :kind Unit
-- Unit ∷ Type

-- >>> :kind 'Unit
-- 'Unit ∷ Unit

-- >>> :kind Maybe Unit
-- Maybe Unit ∷ Type

-- This doesn't make sense and we have to be careful what we really mean, Unit or 'Unit.
-- >>> :kind Maybe 'Unit
-- Expected a type, but 'Unit has kind `Unit'
-- In the first argument of `Maybe', namely 'Unit
-- In the type `Maybe 'Unit'

-- Type-level programming in Haskell without DataKinds is equivalent to programming in a dynamically typed language.
-- By default, having every kind you manipulate be Type is a lot like having all of your terms be of the same type.

-- We can provide a UserType type, whose only purpose is to give us access to its promoted data constructors ('User, 'Admin).
data UserType = RegularUser | Admin

-- >>> :kind 'Admin
-- 'Admin ∷ UserType

-- this won't work
-- newtype User = User {userAdminToken ∷ 'Admin}

-- >>> :kind Proxy
-- Proxy ∷ k → Type

-- >>> :kind Proxy 'Admin
-- Proxy 'Admin ∷ Type

-- >>> :kind Maybe (Proxy 'Admin)
-- Maybe (Proxy 'Admin) ∷ Type

newtype User = User {userAdminToken ∷ Maybe (Proxy 'Admin)}
  deriving (Show)

-- This minor change will cause a type error whenever doSensitiveThings is called without an administration token.
-- TODO: Doesn't make sense to me!
doSensitiveThings ∷ Proxy 'Admin → Int
doSensitiveThings _ = 42

regUser ∷ User
regUser = User Nothing

adminUser ∷ User
adminUser = User (Just Proxy)

-- >>> userAdminToken regUser
-- Nothing

-- >>> userAdminToken adminUser
-- Just Proxy

-- >>> doSensitiveThings (userAdminToken regUser)
-- Couldn't match expected type: Proxy 'Admin
--             with actual type: Maybe (Proxy 'Admin)
-- In the first argument of `doSensitiveThings', namely
--   `(userAdminToken regUser)'
-- In the expression: doSensitiveThings (userAdminToken regUser)
-- In an equation for `it_a1lYr':
--     it_a1lYr = doSensitiveThings (userAdminToken regUser)


-- >>> doSensitiveThings (userAdminToken adminUser)
-- Couldn't match expected type: Proxy 'Admin
--             with actual type: Maybe (Proxy 'Admin)
-- In the first argument of `doSensitiveThings', namely
--   `(userAdminToken adminUser)'
-- In the expression: doSensitiveThings (userAdminToken adminUser)
-- In an equation for `it_a1n5z':
--     it_a1n5z = doSensitiveThings (userAdminToken adminUser)

-- >>> doSensitiveThings Proxy
-- 42

-- With DataKinds enabled almost all types automatically promote to kinds, including the built.in ones.
-- Since built-in types (strings, numbers, lists and tuples) are special at the term-level in terms of syntax,
-- we should expect them to behave oddly at the type-level as well.
-- When playing with promoted built-in types, it's necessary to first import the GHC.TypeLits module.

-- The promoted version of a String is called a SYMBOL.
-- SYMBOLs are NOT lists of characters.
-- Symbol type literals can be written by just using a string literal in a place where a type is expected!

-- >>> :type "hello"
-- "hello" ∷ String

-- >>> :kind "hello"
-- "hello" ∷ Symbol

-- It's somewhat frustrating that SYMBOLs are not merely lists of promoted characters.
-- It means that SYMBOLs are no longer inductive types.
-- It's impossible to deconstruct a SYMBOL, although we are capable of concatenating them via a magic AppendSymbol primitive provided in GHC.TypeLits.

-- >>> :kind AppendSymbol
-- AppendSymbol ∷ Symbol → Symbol → Symbol

-- >>> :kind AppendSymbol "thinking" " with types"
-- AppendSymbol "thinking" " with types" ∷ Symbol

-- >>> :kind! AppendSymbol "thinking" " with types"
-- AppendSymbol "thinking" " with types" ∷ Symbol
-- = "thinking with types"

-- Additionally, we are capable of comparing SYMBOLs via the CmpSymbol primitive.

-- Note: ORDERING is the DataKinds promoted version of the standard Ordering type!
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

-- Promotion of numbers:
-- Only the natural numbers (0, 1, 2, . . .) can be promoted.
-- These natural numbers are of kind Natural.

-- >>> :kind 5085072209
-- 5085072209 ∷ Natural

-- >>> :kind! 5085072209
-- 5085072209 ∷ Natural
-- = 5085072209

-- GHC.TypeLits defines primitives for performing arithmetic on Naturals with exactly the same symbolic identifiers you'd expect them to have.
-- Using them will require enabling TypeOperators.

-- >>> :kind! (1 + 17) * 3
-- (1 + 17) * 3 ∷ Natural
-- = 54

-- >>> :kind! (128 `Div ` 8) ^ 2
-- (128 `Div ` 8) ^ 2 ∷ Natural
-- = 256

-- If lists were defined as library code, without any special syntax, they'd have the following definition:
-- (Because lists' data constructors have symbolic names, they also require TypeOperators enabled.)
-- data [a] = [] | a : [a]

-- This is exactly what the promoted data constructors of lists look like:
-- >>> :kind! '[]
-- '[] ∷ [a]
-- = '[]

-- >>> :kind! '(:)
-- '(:) ∷ a → [a] → [a]
-- = (':)

-- [Bool] is of kind Type and describes a term-level list of booleans.
-- The type '[Bool] is of kind [Type] and describes a type-level list with ONE(!) element (namely, the type Bool.)

-- >>> :kind [Bool]
-- [Bool] ∷ Type

-- >>> :kind '[Bool]
-- '[Bool] ∷ [Type]

-- Due to the way GHC's lexer parses character literals ('a'), make sure you add a space after starting a promoted list.

-- >>> :kind '[ 'True ]
-- '[ 'True ] ∷ [Bool]

-- >>> :kind '['True ]
-- parse error on input `]'

-- Tuples promote straightforwardly via the '(,) constructor.
-- Tuples are promoted with a leading tick.

-- >>> :kind '(2 , "tuple")
-- '(2 , "tuple") ∷ (Natural, Symbol)

-- >>> :kind '(2 , "tuple", 'c')
-- '(2 , "tuple", 'c') ∷ (Natural, Symbol, Char)

-- Where DataKinds really begins to shine is through the introduction of closed type families.
-- You can think of closed type families as functions at the type-level.
-- CmpSymbol, Div, ... are all closed type families.

-- The ability to write closed type families isn't merely one bestowed upon GHC developers.
-- We are capable of writing our own too!

-- Unlike data constructors, we're unfortunately unable to automatically promote term-level functions into type-level ones.
-- However, after enabling TypeFamilies, we can instead "promote" or by explicitly duplicating this logic and writing a completely separate, closed type family.
-- You can think of closed type families as functions at the type-level!
-- Type families are like functions for types.

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

type And ∷ Bool → Bool → Bool
type family And x y where
  And 'True y = y
  And 'False y = 'False

-- While the metaphor between type families and functions is enticing, it isn't entirely correct.
-- The analogues break down in several ways, but the most important one is that type families must be SATURATED.
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

-- type Map ∷ (a → b) → [a] → [b]
-- type family Map f xs where
--   Map _ '[] = '[]
--   Map f (x ': xs) = f x ': Map f xs

-- Because we're unable to partially apply closed type families, Map doesn't turn out to be particularly useful.
-- >>> :type undefined ∷ Proxy (Map (Or 'True))
-- The type family `Map' should have 2 arguments, but has been given 1
-- In an expression type signature: Proxy (Map (Or 'True))
-- In the expression: undefined ∷ Proxy (Map (Or 'True))

-- >>> :type undefined ∷ Proxy (Or 'True)
-- The type family `Or' should have 2 arguments, but has been given 1
-- In an expression type signature: Proxy (Or 'True)
-- In the expression: undefined ∷ Proxy (Or 'True)

-- The kind you write after the `∷` is the kind of the type returned by the type family, not the kind of the type family itself.

type Foo ∷ Bool → Bool → Bool
type family Foo x y

type family Bar x y ∷ Bool → Bool → Bool

-- >>> :kind Foo
-- Foo ∷ Bool → Bool → Bool

-- >>> :kind Bar
-- Bar ∷ Type → Type → Bool → Bool → Bool

---------------
-- Exercises --
---------------

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

-- Exercise 2.4-i

-- regular version
not ∷ Bool → Bool
not True = False
not False = True

type Not ∷ Bool → Bool
type family Not x where
  Not 'True = 'False
  Not 'False = 'True

