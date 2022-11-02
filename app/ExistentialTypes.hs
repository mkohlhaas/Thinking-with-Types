{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

---------------------------------
-- Chapter 7: ExistentialTypes --
---------------------------------

-- 7.1   Existential Types and Eliminators
-- 7.1.1 Dynamic Types
-- 7.1.2 Generalized Constraint Kinded Existentials
-- 7.2   Scoping Information Existentials (in separate file app/ST.hs)

module ExistentialTypes where

import Data.Foldable (asum)
import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Typeable (Typeable, cast, typeRep)

-------------------------------------------
-- 7.1 Existential Types and Eliminators --
-------------------------------------------

-- An existential data type is one that is not defined in terms of a concrete type,
-- but in terms of a quantified type variable (a type variable with ∀), introduced on
-- the right-hand side of the data declaration.

-- Existential types have sort of an identity problem - the type system has forgotten what they are!

---------
-- Any --
---------

-- A simple example for introduction:
-- `Any` is an EXISTENTIAL TYPE and is capable of storing a value of any type and forgets what type it has.
-- The type constructor doesn't have any type variables, and so it can't remember anything.
-- This `a` type exists only within the context of the Any data constructor; it is EXISTENTIAL!
-- Looks like the opposite of a phantom type.
data Any = ∀ a. Any a

-- # GADTAny
-- GADTs provide a more idiomatic syntax for this construction.
data Any' where
  Any' ∷ a → Any'

-- We can use Any to define a list with values of any types.
-- Its usefulness is limited due to the fact that its values can never be recovered.

-- >>> :type [Any 5, Any True, Any "hello"]
-- [Any 5, Any True, Any "hello"] ∷ [Any]

-- Existential types can be eliminated/consumed via continuation-passing.
-- An eliminator is a function which takes a continuation and an existential type that can produce a value regardless of what it gets.
-- Elimination occurs when our existential type is fed into the eliminator.

-- Eliminator for Any.
--       continuation
--             |   existential type
--             |          |
--             |          | resulting value
--             |          |    |
elimAny ∷ (∀ a. a → r) → Any → r
elimAny f (Any a) = f a

-- The caller of elimAny gets to decide the result `r`.
-- But `a` is determined by the type inside of the Any.
-- Functions of type `∀ a. a → r` can only ever return constant values.
-- The polymorphism on their input doesn't allow any form of inspection.

-- >>> elimAny (const 5) (Any [1..5])
-- 5

-- >>> elimAny length (Any [1..5])
-- Couldn't match type `a' with `[a0]' ...

-------------
-- HasShow --
-------------

-- The definition of HasShow is remarkably similar to the GADT definition of Any', with the addition of the `Show a ⇒ constraint`.
-- This constraint requires a Show instance whenever constructing a HasShow, and Haskell will remember this.
-- Because a Show instance was required to build a HasShow, whatever type is inside of HasShow must have a Show instance.
-- Remarkably, Haskell is smart enough to realize this, and allow us to call `show` on whatever type exists inside.
data HasShow where
  HasShow ∷ Show a ⇒ a → HasShow

-- We can use this fact to write a Show instance for HasShow.
instance Show HasShow where
  show ∷ HasShow → String
  show (HasShow a) = show a

-- We are able to write an eliminator for HasShow which knows we have Show in scope.
elimHasShow ∷ (∀ a. Show a ⇒ a → r) → HasShow → r
elimHasShow f (HasShow a) = f a

-- Show instance of HasShow in terms of elimHasShow
-- instance Show HasShow where
--   show ∷ HasShow → String
--   show = elimHasShow show

-- >>> HasShow 5
-- 5

-------------------------
-- 7.1.1 Dynamic Types --
-------------------------

-- The Typeable class provides type information at runtime, and allows for dynamic casting via `cast ∷ (Typeable a, Typeable b) ⇒ a → Maybe b`.
-- We can existentialize Typeable types in order to turn Haskell into a dynamically typed language.

-- Using this approach, we can write Python-style functions that play fast and loose with their types.
-- As an illustration, the `+` operator in Python plays double duty by concatenating strings and adding numbers.
-- We can implement the same function in Haskell with Dynamic.

data Dynamic where
  Dynamic ∷ Typeable t ⇒ t → Dynamic

elimDynamic ∷ (∀ a. Typeable a ⇒ a → r) → Dynamic → r
elimDynamic f (Dynamic a) = f a

-- attempts to cast a Dynamic to an `a`
fromDynamic ∷ Typeable a ⇒ Dynamic → Maybe a
fromDynamic = elimDynamic cast

-- >>> fromDynamic @String (Dynamic "Hello")
-- Just "Hello"

-- lift a regular, strongly-typed function into a function over dynamic types
liftD2 ∷ ∀ a b r. (Typeable a, Typeable b, Typeable r) ⇒ Dynamic → Dynamic → (a → b → r) → Maybe Dynamic
liftD2 d1 d2 f = fmap Dynamic . f <$> fromDynamic @a d1 <*> fromDynamic @b d2

-- Haskell's version of Python's `+` operator
pyPlus ∷ Dynamic → Dynamic → Dynamic
pyPlus d1 d2 =
  fromMaybe (error "bad types for pyPlus") $
    asum -- alternative sum
      [ liftD2 @String @String d1 d2 (++), ----------------------- String concatenation
        liftD2 @Int @Int d1 d2 (+), ------------------------------ Integer addition
        liftD2 @String @Int d1 d2 $ \str int → str ++ show int, -- Concatenating a String and an Integer
        liftD2 @Int @String d1 d2 $ \int str → show int ++ str --- Concatenating an Integer and a String
      ]

-- >>> asum [Just "Hello", Nothing, Just "World"]
-- Just "Hello"

-- >>> asum [Nothing, Nothing, Nothing, Nothing, Just "World"]
-- Just "World"

-- >>> asum [Nothing, Nothing]
-- Nothing

-- >>> default (Int) -- set the default numeric type to Int (to construct Dynamics without type signatures)
-- >>> fromDynamic @Int (pyPlus (Dynamic 1) (Dynamic 2))
-- Just 3

-- >>> :type pyPlus (Dynamic @Int 1) (Dynamic @Int 2)
-- pyPlus (Dynamic @Int 1) (Dynamic @Int 2) ∷ Dynamic

-- >>> fromDynamic @String (pyPlus (Dynamic "hello") (Dynamic " world"))
-- Just "hello world"

-- >>> default (Int)
-- >>> fromDynamic @String (pyPlus (Dynamic 4) (Dynamic " minute"))
-- Just "4 minute"

-- >>> default (Int)
-- >>> fromDynamic @String (pyPlus (Dynamic "minute ") (Dynamic 4))
-- Just "minute 4"

-- >>> fromDynamic @Int (pyPlus (Dynamic "hello") (Dynamic " world"))
-- Nothing

-- >>> fromDynamic @Bool (pyPlus (Dynamic "hello") (Dynamic " world"))
-- Nothing

-- show the actual type of a Dynamic
typeOf ∷ Dynamic → String
typeOf = elimDynamic $ \(_ ∷ t) → show . typeRep $ Proxy @t

-- >>> typeOf (Dynamic 5)
-- "Integer"

-- >>> typeOf (Dynamic "hello")
-- "[Char]"

-- Dynamically typed languages are merely strongly typed languages with a single type! ;-)

------------------------------------------------------
-- 7.1.2 Generalized Constraint Kinded Existentials --
------------------------------------------------------

-- The definitions of HasShow and Dynamic are nearly identical.
-- data HasShow where
--   HasShow ∷ Show a ⇒ a → HasShow

-- data Dynamic where
--   Dynamic ∷ Typeable t ⇒ t → Dynamic

-- a pattern to be factored out
-- By enabling ConstraintKinds, we are able to be polymorphic over Constraints.
data Has (c ∷ Type → Constraint) where
  Has ∷ c t ⇒ t → Has c

-- eliminate any constraint
elimHas ∷ (∀ a. c a ⇒ a → r) → Has c → r
elimHas f (Has a) = f a

-- We can thus implement HasShow and Dynamic as type synonyms/aliases.
type HasShow' = Has Show
type Dynamic' = Has Typeable

-- We want to use multiple constraints at once.
isMempty ∷ (Monoid a, Eq a) ⇒ a → Bool
isMempty a = a == mempty

-- We'd like to construct an Has around this constraint: (Monoid a, Eq a).
-- Unfortunately, there is no type-level lambda syntax, so we're unable to turn this
-- type into something that's curryable.
-- We can try a type synonym:
type MonoidAndEq a = (Monoid a, Eq a)

-- But GHC won't allow us to construct a `Has MonoidAndEq`.
-- >>> :t Has [True] ∷ Has MonoidAndEq
-- The type synonym `MonoidAndEq' should have 1 argument, but has been given none
-- In an expression type signature: Has MonoidAndEq
-- In the expression: Has [True] ∷ Has MonoidAndEq

-- The problem is that type synonyms must always be fully saturated.
-- We're unable to talk about MonoidAndEq in its unsaturated form, only `MonoidAndEq a` is acceptable to the compiler.

-- There is a solution for Constraint synonyms. (Though not for type synonyms in general.)
-- We can instead define a new class with a superclass constraint, and an instance that comes for free given those same constraints.
-- This is known as a CONSTRAINT SYNONYM.
-- While type synonyms are unable to be partially applied, classes have no such restriction!
class (Monoid a, Eq a) ⇒ MonoidEq a

instance (Monoid a, Eq a) ⇒ MonoidEq a

-- >>> let hasMonoidEq = Has ["hello"] ∷ Has MonoidEq
-- >>> :type elimHas isMempty hasMonoidEq
-- elimHas isMempty hasMonoidEq ∷ Bool

-- >>> let hasMonoidEq = Has [] ∷ Has MonoidEq
-- >>> elimHas isMempty hasMonoidEq
-- True

-- >>> let hasMonoidEq = Has ["hello"] ∷ Has MonoidEq
-- >>> elimHas isMempty hasMonoidEq
-- False

