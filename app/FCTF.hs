{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}

-- First Class Type Families
-- We can write a defunctionalized symbol whose type corresponds to the desired type-level function.

module FCTF where

import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe)
import GHC.TypeLits (type (+))

-- kind synonym which describes a type-level function which, when evaluated, will produce a type of kind A
type Exp a = a → Type

-- >>> :kind Exp
-- Exp ∷ Type → Type

-- Eval matches on `Exp a` mapping them to an A.
type family Eval (e ∷ Exp a) ∷ a

---------
-- Snd --
---------

-- To lift `snd` to the type level, we write a data type whose kind mirrors the type of snd.
data Snd ∷ (a, b) → Exp b

-- >>> :type snd
-- snd ∷ (a, b) → b

-- >>> :kind Snd
-- Snd ∷ (a, b) → b → Type

-- Eval Snd
type instance Eval (Snd '(a, b)) = b

-- Note the promoted pair.
-- >>> :kind! Eval (Snd '(1, "hello"))
-- Eval (Snd '(1, "hello")) ∷ Symbol
-- = "hello"

---------------
-- FromMaybe --
---------------

-- Functions that perform PATTERN MATCHING can be lifted to the defunctionalized style by providing multiple type instances for Eval.

-- fromMaybe ∷ ∀ a. a → Maybe a → a

def ∷ String
def = fromMaybe "default" Nothing

-- >>> def
-- "default"

data FromMaybe ∷ a → Maybe a → Exp a

-- pattern matching on `Maybe a`
type instance Eval (FromMaybe a 'Nothing) = a

type instance Eval (FromMaybe _1 ('Just a)) = a

-- >>> :kind! Eval(FromMaybe "nothing" 'Nothing)
-- Eval(FromMaybe "nothing" 'Nothing) ∷ Symbol
-- = "nothing"

-- >>> :kind! Eval(FromMaybe "nothing" ('Just "just"))
-- Eval(FromMaybe "nothing" ('Just "just")) ∷ Symbol
-- = "just"

-----------------
-- ListToMaybe --
-----------------

-- Exercise 10.2-i: Defunctionalize listToMaybe at the type-level.
listToMaybe ∷ [a] → Maybe a
listToMaybe [] = Nothing
listToMaybe (x : _) = Just x

data ListToMaybe ∷ [a] → Exp (Maybe a)

type instance Eval (ListToMaybe '[]) = 'Nothing

type instance Eval (ListToMaybe (a ': _)) = 'Just a

-- >>> :kind! Eval (ListToMaybe '[])
-- Eval (ListToMaybe '[]) ∷ Maybe a
-- = 'Nothing

--------------
-- Map List --
--------------

mapList ∷ (a → b) → [a] → [b]
mapList _ [] = []
mapList f (a : as) = f a : mapList f as

data MapList ∷ (a → Exp b) → [a] → Exp [b]

-- Eval Nil
type instance Eval (MapList f '[]) = '[]

-- Eval Cons
type instance Eval (MapList f (a ': as)) = Eval (f a) ': Eval (MapList f as)

-- >>> :kind! Eval(MapList (FromMaybe 0) ['Nothing, ('Just 1)])
-- Eval(MapList (FromMaybe 0) ['Nothing, ('Just 1)]) ∷ [Natural]
-- = '[0, 1]

-------------------------
-- Ad-Hoc Polymorphism --
-------------------------

---------
-- Map --
---------

-- higher-order functions

-- generalizing MapList
data Map ∷ (a → Exp b) → f a → Exp (f b)

-- Because type families are capable of discriminating on types, we can write several instances of Eval for Map!

--------------------
-- Map List again --
--------------------

type instance Eval (Map f '[]) = '[]

type instance Eval (Map f (a ': as)) = Eval (f a) ': Eval (Map f as)

-- >>> :kind! Eval(Map (FromMaybe 0) ['Nothing, ('Just 1)])
-- Eval(Map (FromMaybe 0) ['Nothing, ('Just 1)]) ∷ [Natural]
-- = '[0, 1]

---------
-- Sum --
---------

-- a littler helper function
data Sum ∷ a → a → Exp a

type instance Eval (Sum a b) = a + b

-- >>> :kind! Eval (Sum 2 3)
-- Eval (Sum 2 3) :: Natural
-- = 5

---------------
-- Map Maybe --
---------------

type instance Eval (Map f 'Nothing) = 'Nothing

type instance Eval (Map f ('Just a)) = 'Just (Eval (f a))

-- >>> :kind! Eval(Map (Sum 3) 'Nothing)
-- Eval(Map (Sum 3) 'Nothing) :: Maybe Natural
-- = 'Nothing

-- >>> :kind! Eval(Map (Sum 3) ('Just 5))
-- Eval(Map (Sum 3) ('Just 5)) :: Maybe Natural
-- = 'Just 8

----------------
-- Map Either --
----------------

type instance Eval (Map f ('Left a)) = 'Left a

type instance Eval (Map f ('Right b)) = 'Right (Eval (f b))

-- >>> :kind! Eval(Map (Sum 3) ('Left 5))
-- Eval(Map (Sum 3) ('Left 5)) :: Either Natural Natural
-- = 'Left 5

-- >>> :kind! Eval(Map (Sum 3) ('Right 5))
-- Eval(Map (Sum 3) ('Right 5)) :: Either a Natural
-- = 'Right 8

---------------
-- Map Tuple --
---------------

type instance Eval (Map f '(a, b)) = '(a, Eval (f b))

-- >>> :kind! Eval(Map (Sum 3) '(4, 5))
-- Eval(Map (Sum 3) '(4, 5)) :: (Natural, Natural)
-- = '(4, 8)

----------
-- (++) --
----------

-- can be used to append types
data (++) ∷ [a] → [a] → Exp [a]

type instance Eval ((++) '[] ys) = ys

type instance Eval ((++) (x ': xs) ys) = x ': Eval ((++) xs ys)

-- >>> :kind! Eval('[Int, Int, Int] ++ '[Bool, Bool, Bool])
-- Eval('[Int, Int, Int] ++ '[Bool, Bool, Bool]) :: [Type]
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
-- Eval(Mappend '[Int, Int, Int] '[Bool, Bool, Bool]) :: [Type]
-- = '[Int, Int, Int, Bool, Bool, Bool]

-- appending Constraints
-- >>> :kind! Eval(Mappend (Eq Int) (Eq Bool))
-- Eval(Mappend (Eq Int) (Eq Bool)) :: Constraint
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
-- Eval(Mappend (Eq Int) (Eval (Mempty (Eq Bool)))) :: Constraint
-- = (Eq Int, () :: Constraint)

-----------
-- Foldr --
-----------

-- Exercise 10.2-ii: Defunctionalize `foldr ∷ (a → b → b) → b → [a] → b`.
data Foldr ∷ (a → b → Exp b) → b → [a] → Exp b

-- pattern-matching on empty list
type instance Eval (Foldr _ b '[]) = b

-- pattern-matching on non-empty list
type instance Eval (Foldr f b (a ': as)) = Eval (f a (Eval (Foldr f b as)))

-- >>> :kind! Eval(Foldr Sum 0 '[1, 2, 3, 4, 5])
-- Eval(Foldr Sum 0 '[1, 2, 3, 4, 5]) :: Natural
-- = 15

---------------------------------------
-- Working with First Class Families --
---------------------------------------

----------
-- Pure --
----------

data Pure ∷ a → Exp a

type instance Eval (Pure x) = x

-- >>> :kind! Eval(Pure "hello")
-- Eval(Pure "hello") :: Symbol
-- = "hello"

------------------
-- (=<<) - bind --
------------------

-- First class families (FCF) form a monad at the type-level!

data (=<<) ∷ (a → Exp b) → Exp a → Exp b

type instance Eval (k =<< e) = Eval (k (Eval e))

infixr 0 =<<

--------------------
-- (<=<) - Kleisli --
--------------------

{- ORMOLU_DISABLE -}

-- We can compose FCFs in terms of their Kleisli composition.
-- Traditionally the fish operator (<=<) is used to represent this combinator in Haskell.
-- We are unable to use the more familiar period operator at the type-level, as it conflicts with the syntax of the forall quantifier.

-- fish operator
data (<=<) ∷ (b → Exp c) → (a → Exp b) → a → Exp c

type instance Eval ((f <=< g) x) = Eval (f (Eval (g x)))

infixr 1 <=<

-- >>> type Snd2 = Snd <=< Snd
-- >>> :kind! Eval(Snd2 '(1 ,'(2 , 3)))
-- Eval(Snd2 '(1 ,'(2 , 3))) :: Natural
-- = 3

-- At the type-level (<=<) acts like regular function composition (.),
-- while (=<<) behaves like function application ($).

-- >>> :kind! Eval(Snd <=< FromMaybe '(0 , 1) =<< Pure(Nothing))
-- Eval(Snd <=< FromMaybe '(0 , 1) =<< Pure(Nothing)) :: Natural
-- = 1

-- >>> :kind! Eval(Snd <=< FromMaybe '(0 , 0) =<< Pure(Just '(2 , 3)))
-- Eval(Snd <=< FromMaybe '(0 , 0) =<< Pure(Just '(2 , 3))) :: Natural
-- = 3

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
-- Eval(TyEq Int Int) :: Bool
-- = 'True

-- >>> :kind! Eval(TyEq Int String)
-- Eval(TyEq Int String) :: Bool
-- = 'False

--------------
-- Collapse --
--------------

-- collapsing lists of CONSTRAINTs

data Collapse ∷ [Constraint] → Exp Constraint

type instance Eval (Collapse '[]) = (() ∷ Constraint)

type instance Eval (Collapse (a ': as)) = (a, Eval (Collapse as))

-----------
-- Pure1 --
-----------

-- a little helper (e.g. for MapList) for transforming functions `(a → b) → (a → Exp b)`
data Pure1 ∷ (a → b) → a → Exp b

type instance Eval (Pure1 f x) = f x

-- >>> :kind! Eval(Pure1 Eq Int)
-- Eval(Pure1 Eq Int) :: Constraint
-- = Eq Int

---------
-- All --
---------

type All (c ∷ k → Constraint) (ts ∷ [k]) = Collapse =<< MapList (Pure1 c) ts

-- Much nicer implementation of All than chapter 5's.
-- >>> :kind! Eval(All Eq '[Int , Bool])
-- Eval(All Eq '[Int , Bool]) :: Constraint
-- = (Eq Int, (Eq Bool, () :: Constraint))

-----------
-- Pure2 --
-----------

data Pure2 ∷ (a → b → c) → a → b → Exp c

type instance Eval (Pure2 f x y) = f x y

-- >>> :kind! Eval(Pure2 Sum 1 2)
-- Eval(Pure2 Sum 1 2) :: Natural -> Type
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

{-

-- ???
data Fmap ∷ (a → b) → Exp a → Exp b

type instance Eval (Fmap f fa) = f (Eval fa)

-}

