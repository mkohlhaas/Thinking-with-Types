{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# HLINT ignore "Unused LANGUAGE pragma" #-}

--------------------------------------------
-- Chapter 10: First Class Families (FCF) --
--------------------------------------------

-- 10.1 Defunctionalization
-- 10.2 Type-Level Defunctionalization
-- 10.3 Working with First Class Families
-- 10.4 Ad-Hoc Polymorphism

module FCTF where

import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe, listToMaybe)
import GHC.TypeLits (type (+))

-----------------------------------------
-- 10.2 Type-Level Defunctionalization --
-----------------------------------------

-- `Exp a` describes a type-level function
type Exp a = a → Type

-- >>> :kind Exp
-- Exp ∷ Type → Type

-- >>> :kind Exp Int
-- Exp Int ∷ Type

-- Evaluation is performed via an open type family Eval.
type family Eval (e ∷ Exp a) ∷ a

-------------------------------------
-- Lifting `fst` to the Type Level --
-------------------------------------

-- >>> :type fst
-- fst ∷ (a, b) → a

-- >>> fst (1, "hello")
-- 1

-- Empty data types are used to write defunctionalized labels.
data Fst ∷ (a, b) → Exp a

-- >>> :kind Fst
-- Fst ∷ (a, b) → a → Type

-- The types of `fst` and `Fst` look very similar.
-- `Fst` just has `→ Type` appended.

-- Fst doesn't have a data constructor.
-- We are strictly operating at the type level.
-- >>> Fst (1, "hello")
-- Illegal term-level use of the type constructor `Fst' ...

-- Eval Fst
-- We need to "evaluate" it with an instance of the open type family `Eval`.
type instance Eval (Fst '(a, b)) = a

-- Evaluation can forced in the Repl with `:kind!`.
-- >>> :kind! Eval (Fst '(1, "hello"))
-- Eval (Fst '(1, "hello")) ∷ Natural
-- = 1

-- >>> :kind! Eval (Fst '("hello", 1))
-- Eval (Fst '("hello", 1)) ∷ Symbol
-- = "hello"

---------------
-- FromMaybe --
---------------

-- >>> :type fromMaybe
-- fromMaybe ∷ a → Maybe a → a

-- >>> fromMaybe "default" Nothing
-- "default"

-- >>> fromMaybe "default" (Just "hello")
-- "hello"

-- defunctionalization
data FromMaybe ∷ a → Maybe a → Exp a

-- >>> :kind FromMaybe
-- FromMaybe ∷ a → Maybe a → a → Type

-- Functions like `fromMaybe` that perform PATTERN MATCHING can be lifted to the defunctionalized style by providing multiple type instances for Eval.
-- pattern matching on `Maybe a`
type instance Eval (FromMaybe a 'Nothing) = a

type instance Eval (FromMaybe _ ('Just a)) = a

-- >>> :kind! Eval(FromMaybe "default" 'Nothing)
-- Eval(FromMaybe "default" 'Nothing) ∷ Symbol
-- = "default"

-- >>> :kind! Eval(FromMaybe "default" ('Just "hello"))
-- Eval(FromMaybe "default" ('Just "hello")) ∷ Symbol
-- = "hello"

-----------------
-- ListToMaybe --
-----------------

-- Exercise 10.2-i: Defunctionalize listToMaybe at the type-level.

-- listToMaybe ∷ [a] → Maybe a
-- listToMaybe [] = Nothing
-- listToMaybe (x : _) = Just x

-- >>> :type listToMaybe
-- listToMaybe ∷ [a] → Maybe a

-- defunctionalization
data ListToMaybe ∷ [a] → Exp (Maybe a)

type instance Eval (ListToMaybe '[]) = 'Nothing

type instance Eval (ListToMaybe (a ': _)) = 'Just a

-- >>> :kind! Eval (ListToMaybe '[])
-- Eval (ListToMaybe '[]) ∷ Maybe a
-- = 'Nothing

-- >>> :kind! Eval (ListToMaybe '["hello", "world"])
-- Eval (ListToMaybe '["hello", "world"]) ∷ Maybe Symbol
-- = 'Just "hello"

--------------
-- Map List --
--------------

-- Defunctionalization at the type-level allows for higher-order functions!

mapList ∷ (a → b) → [a] → [b]
mapList _ [] = []
mapList f (a : as) = f a : mapList f as

data MapList ∷ (a → Exp b) → [a] → Exp [b]

-- Eval Nil
type instance Eval (MapList _ '[]) = '[]

-- Eval Cons
type instance Eval (MapList f (a ': as)) = Eval (f a) ': Eval (MapList f as)

-- >>> :kind! Eval(MapList (FromMaybe 0) '[])
-- Eval(MapList (FromMaybe 0) '[]) ∷ [Natural]
-- = '[]

-- side note: no tick needed for the list.
-- >>> :kind! Eval(MapList (FromMaybe 0) ['Nothing, ('Just 1)])
-- Eval(MapList (FromMaybe 0) '[ 'Nothing, ('Just 1)]) ∷ [Natural]
-- = '[0, 1]

---------------------------------------------------------------------------
-- Exercise 10.2-ii: Defunctionalize `foldr ∷ (a → b → b) → b → [a] → b` --
---------------------------------------------------------------------------

-- >>> :type foldr
-- foldr ∷ Foldable t ⇒ (a → b → b) → b → t a → b

-- foldr for lists
-- >>> :type foldr @[]
-- foldr @[] ∷ (a → b → b) → b → [a] → b

-- defunctionalization
data Foldr ∷ (a → b → Exp b) → b → [a] → Exp b

-- pattern-matching on empty list
type instance Eval (Foldr _ b '[]) = b

-- pattern-matching on non-empty list
type instance Eval (Foldr f b (a ': as)) = Eval (f a (Eval (Foldr f b as)))

-- >>> :kind! Eval(Foldr Sum 0 '[1, 2, 3, 4, 5])
-- Eval(Foldr Sum 0 '[1, 2, 3, 4, 5]) ∷ Natural
-- = 15

--------------------------------------------
-- 10.3 Working with First Class Families --
--------------------------------------------

----------
-- Pure --
----------

data Pure ∷ a → Exp a

type instance Eval (Pure x) = x

-- >>> :kind! Eval(Pure 5)
-- Eval(Pure 5) ∷ Natural
-- = 5

-- >>> :kind! Eval(Pure "hello")
-- Eval(Pure "hello") ∷ Symbol
-- = "hello"

----------------------------------------------
-- (=<<) - bind with arguments interchanged --
----------------------------------------------

-- First class families (FCFs) form a monad at the type-level!!

data (=<<) ∷ (a → Exp b) → Exp a → Exp b

type instance Eval (k =<< e) = Eval (k (Eval e))

infixr 0 =<<

---------------------
-- (<=<) - Kleisli --
---------------------

{- ORMOLU_DISABLE -}

-- We can compose FCFs in terms of their Kleisli composition.
-- Traditionally the fish operator (<=<) is used to represent this combinator in Haskell.
-- We are unable to use the more familiar period operator at the type-level, as it conflicts with the syntax of the ∀ quantifier.

-- fish operator
data (<=<) ∷ (b → Exp c) → (a → Exp b) → a → Exp c

type instance Eval ((f <=< g) x) = Eval (f (Eval (g x)))

infixr 1 <=<

-- >>> type Fst2 = Fst <=< Fst
-- >>> :kind! Eval(Fst2 '( '(2 , 3), 1))
-- Eval(Fst2 '( '(2 , 3), 1)) :: Natural
-- = 2

-- At the type-level (<=<) acts like regular function composition (.), while (=<<) behaves like function application ($).

-- Remember:
-- fish operator (<=<) ≅ function composition (.)
-- reverse bind  (=<<) ≅ function application ($)

-- >>> :kind! Eval(Snd <=< FromMaybe '(0 , 1) =<< Pure(Nothing))
-- Eval(Snd ⇐< FromMaybe '(0 , 1) =<< Pure(Nothing)) ∷ Natural
-- = 1

-- >>> :kind! Eval(Fst <=< FromMaybe '(0 , 0) =<< Pure(Just '(2 , 3)))
-- Eval(Fst <=< FromMaybe '(0 , 0) =<< Pure(Just '(2 , 3))) :: Natural
-- = 2

{- ORMOLU_ENABLE -}

----------
-- TyEq --
----------

-- The [first-class-families](https://hackage.haskell.org/package/first-class-families) package provides most of Prelude as FCFs,
-- as well as some particularly useful functions for type-level programming.
-- E.g., we can determine if any two types are the same - remember, there is no Eq at the type-level!

data TyEq ∷ a → b → Exp Bool

-- Eval TyEq
type instance Eval (TyEq a b) = TyEqImpl a b

type family TyEqImpl (a ∷ k) (b ∷ k) ∷ Bool where
  TyEqImpl a a = 'True
  TyEqImpl a b = 'False

-- >>> :kind! Eval(TyEq Int Int)
-- Eval(TyEq Int Int) ∷ Bool
-- = 'True

-- >>> :kind! Eval(TyEq Int String)
-- Eval(TyEq Int String) ∷ Bool
-- = 'False

-----------------
-- Constraints --
-----------------

-- Collapsing/Conjunction lists of constraints.

data Constraints ∷ [Constraint] → Exp Constraint

type instance Eval (Constraints '[]) = (() ∷ Constraint)

type instance Eval (Constraints (a ': as)) = (a, Eval (Constraints as))

-----------
-- Pure1 --
-----------

-- a little helper (e.g. for MapList) for transforming functions `(a → b) → (a → Exp b)`
data Pure1 ∷ (a → b) → a → Exp b

type instance Eval (Pure1 f x) = f x

-- >>> :kind! Eval(Pure1 Eq Int)
-- Eval(Pure1 Eq Int) ∷ Constraint
-- = Eq Int

---------
-- All --
---------

type All (c ∷ k → Constraint) (ts ∷ [k]) = Constraints =<< MapList (Pure1 c) ts

-- Much nicer implementation of All than chapter 5's.
-- >>> :kind! Eval(All Eq '[Int , Bool])
-- Eval(All Eq '[Int , Bool]) ∷ Constraint
-- = (Eq Int, (Eq Bool, () ∷ Constraint))

-----------
-- Pure2 --
-----------

data Pure2 ∷ (a → b → c) → a → b → Exp c

type instance Eval (Pure2 f x y) = f x y

-- >>> :kind! Eval(Pure2 Sum 1 2)
-- Eval(Pure2 Sum 1 2) ∷ Natural → Type
-- = Sum 1 2

-----------
-- Pure3 --
-----------

data Pure3 ∷ (a → b → c → d) → a → b → c → Exp d

type instance Eval (Pure3 f x y z) = f x y z

----------
-- Join --
----------

data Join ∷ Exp (Exp a) → Exp a

type instance Eval (Join e) = Eval (Eval e)

---------
-- ($) --
---------

data ($) ∷ (a → Exp b) → a → Exp b

type instance Eval (($) f a) = Eval (f a)

infixr 0 $

----------
-- Flip --
----------

data Flip ∷ (a → b → Exp c) → b → a → Exp c

type instance Eval (Flip f y x) = Eval (f x y)

------------------------------
-- 10.4 Ad-Hoc Polymorphism --
------------------------------

---------
-- Map --
---------

-- higher-order functions

-- >>> :type fmap
-- fmap :: Functor f => (a -> b) -> f a -> f b

-- defunctionalization
data Map ∷ (a → Exp b) → f a → Exp (f b)

-- Because type families are capable of discriminating on types, we can write several instances of Eval for Map!
-- E.g. Map List, Map Maybe, Map Either, Map Tuple ...

--------------------
-- Map List again --
--------------------

type instance Eval (Map f '[]) = '[]

type instance Eval (Map f (a ': as)) = Eval (f a) ': Eval (Map f as)

-- >>> :kind! Eval(Map (FromMaybe 0) ['Nothing, ('Just 1)])
-- Eval(Map (FromMaybe 0) ['Nothing, ('Just 1)]) ∷ [Natural]
-- = '[0, 1]

----------
-- (:+) --
----------

-- >>> :type (+)
-- (+) :: Num a => a -> a -> a

-- a littler helper function
data (:+) ∷ a → a → Exp a

type instance Eval ((:+) a b) = a + b

-- >>> :kind! Eval ((+) 2 3)
-- Eval ((:+) 2 3) :: Natural
-- = 5

---------------
-- Map Maybe --
---------------

type instance Eval (Map f 'Nothing) = 'Nothing

type instance Eval (Map f ('Just a)) = 'Just (Eval (f a))

-- >>> :kind! Eval(Map ((:+) 3) 'Nothing)
-- Eval(Map ((:+) 3) 'Nothing) :: Maybe Natural
-- = 'Nothing

-- >>> :kind! Eval(Map ((:+) 3) ('Just 5))
-- Eval(Map ((:+) 3) ('Just 5)) :: Maybe Natural
-- = 'Just 8

----------------
-- Map Either --
----------------

type instance Eval (Map f ('Left a)) = 'Left a

type instance Eval (Map f ('Right b)) = 'Right (Eval (f b))

-- >>> :kind! Eval(Map ((:+) 3) ('Left 5))
-- Eval(Map ((:+) 3) ('Left 5)) :: Either Natural Natural
-- = 'Left 5

-- >>> :kind! Eval(Map ((:+) 3) ('Right 5))
-- Eval(Map ((:+) 3) ('Right 5)) :: Either a Natural
-- = 'Right 8

---------------
-- Map Tuple --
---------------

type instance Eval (Map f '(a, b)) = '(a, Eval (f b))

-- >>> :kind! Eval(Map ((:+) 3) '(4, 5))
-- Eval(Map ((:+) 3) '(4, 5)) :: (Natural, Natural)
-- = '(4, 8)

----------
-- (++) --
----------

-- >>> :type (++)
-- (++) :: [a] -> [a] -> [a]

-- can be used to append types
data (++) ∷ [a] → [a] → Exp [a]

type instance Eval ((++) '[] ys) = ys

type instance Eval ((++) (x ': xs) ys) = x ': Eval ((++) xs ys)

-- >>> :kind! Eval('[Int, Int, Int] ++ '[Bool, Bool, Bool])
-- Eval('[Int, Int, Int] ++ '[Bool, Bool, Bool]) ∷ [Type]
-- = '[Int, Int, Int, Bool, Bool, Bool]

-------------
-- Mappend --
-------------

-- semigroup operation Mappend to append Constraints
data Mappend ∷ a → a → Exp a

-- pair
type instance Eval (Mappend '() '()) = '()

-- Constraint
type instance Eval (Mappend (a ∷ Constraint) (b ∷ Constraint)) = (a, b)

-- list
type instance Eval (Mappend (a ∷ [k]) (b ∷ [k])) = Eval (a ++ b)

-- appending types
-- >>> :kind! Eval(Mappend '[Int, Int, Int] '[Bool, Bool, Bool])
-- Eval(Mappend '[Int, Int, Int] '[Bool, Bool, Bool]) ∷ [Type]
-- = '[Int, Int, Int, Bool, Bool, Bool]

-- appending Constraints
-- >>> :kind! Eval(Mappend (Eq Int) (Eq Bool))
-- Eval(Mappend (Eq Int) (Eq Bool)) ∷ Constraint
-- = (Eq Int, Eq Bool)

------------
-- Mempty --
------------

-- Type families are not allowed to discriminate on their return type.
-- "Data type has non-* return kind ‘k’"
-- data Mempty ∷ k

-- making the "type application" explicit
data Mempty ∷ k → Exp k

-- Given a type of any monoidal kind K, Mempty will give back the monoidal identity for that kind.

-- empty pair
type instance Eval (Mempty '()) = '()

-- empty Constraint
type instance Eval (Mempty (c ∷ Constraint)) = (() ∷ Constraint)

-- empty list
type instance Eval (Mempty (l ∷ [k])) = '[]

-- Mempty acts more like an annihilator
-- >>> :kind! Eval(Mappend (Eq Int) (Eval (Mempty (Eq Bool))))
-- Eval(Mappend (Eq Int) (Eval (Mempty (Eq Bool)))) ∷ Constraint
-- = (Eq Int, () ∷ Constraint)

