{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

----------------------
-- Chapter 8: Roles --
----------------------

-- 8.1 Coercions
-- 8.2 Roles

module Roles where

import Data.Coerce (Coercible, coerce)
import Data.Map (Map, singleton)
import Data.Monoid (Product (..), Sum (..))

---------------------
-- 8.1 Coercisions --
---------------------

newtype ZipList a = ZipList
  { getZipList ∷ [a]
  }
  deriving (Show)

-- In Haskell, newtypes are guaranteed to be a zero-cost abstraction.
-- All the following values are representationally equal.
-- They have exactly the same physical representation in memory.

-- >>> [54, 46]
-- [54,46]

-- >>> [Sum 54, Sum 46]
-- [Sum {getSum = 54},Sum {getSum = 46}]

-- >>> ZipList [54, 46]
-- ZipList {getZipList = [54,46]}

-- >>> ZipList [Sum 54, Sum 46]
-- ZipList {getZipList = [Sum {getSum = 54},Sum {getSum = 46}]}

-- This zero-cost property of newtypes has profound implications on performance.
-- It gives us the ability to reinterpret a value of one type as a value of another and do it in O(0) time.

-- The `Coercible a b` constraint is a proof that the types `a` and `b` have the same runtime representation.
-- coerce ∷ Coercible a b ⇒ a → b

-- Coercible is a magic constraint.
-- The compiler will write instances of it for you and insists on this.
-- You cannot write your own!

-- >>> instance Coercible a b
-- Class `Coercible' does not support user-specified instances ...

-- If we wanted to sum a list of Ints, we could use the Sum Int monoid instance.
-- Requires traversing the entire list with an fmap just in order to get the right Monoid instance in scope.
slowSum ∷ [Int] → Int
slowSum = getSum . mconcat . fmap Sum

-- >>> fmap Sum [1..5]
-- >>> mconcat $ fmap Sum [1..5]
-- >>> slowSum [1..5]
-- [Sum {getSum = 1},Sum {getSum = 2},Sum {getSum = 3},Sum {getSum = 4},Sum {getSum = 5}]
-- Sum {getSum = 15}
-- 15

-- `coerce` can be used to massage data from one type into another without paying any runtime costs.
-- Using `coerce` to transform `[Int]` into `[Sum Int]` in O(0) time, giving us access to the right Monoid for free.
fastSum ∷ [Int] → Int
fastSum = getSum . mconcat . coerce

-- >>> fastSum [1..5]
-- 15

-- General RULE: if you ever find yourself writing `fmap TypeConstructor`, it should be replaced with coerce (unless the functor instance is polymorphic).

-- Coercible corresponds to representational equality.
-- Laws of equality:
-- - Reflexivity: `Coercible a a` = true ∀ a.
-- - Symmetry:    `Coercible a b` ⇒ `Coercible b a`.
-- - Transitivity: Given `Coercible a b` and `Coercible b c` ⇒ `Coercible a c`.

sumToProd ∷ Product Int
sumToProd = coerce (1867 ∷ Sum Int)

-- So it's perfectly acceptable to coerce a Sum a into a Product a.
-- >>> sumToProd
-- Product {getProduct = 1867}

-- Qustion: Are representationally equal types always safely interchangeable?
-- Answer:  They're not! E.g.
-- insert ∷ Ord k ⇒ k → v → Map k v → Map k v
-- `Map k v` is a container providing map lookups with key k and value v.
-- It's represented as a balanced tree, ordered via an Ord k instance.
-- `Map k v`s layout in memory is entirely dependent on the Ord k instance it was built with.

-- Reverse flips around an underlying Ord instance.
newtype Reverse a = Reverse {getReverse ∷ a}
  deriving (Eq, Show)

instance Ord a ⇒ Ord (Reverse a) where
  compare ∷ Ord a ⇒ Reverse a → Reverse a → Ordering
  compare (Reverse a) (Reverse b) = compare b a

-- `Reverse a` is safely Coercible with `a`.
-- It's not the case that  `Map k v`can be safely coerced to `Map (Reverse k) v`.
-- They have completely different layouts in memory!

-- Note: The layout of `Map k v` does not depend on `v`.
-- We are free to safely coerce `Map k v` as `Map k v'`.

-- a map with a single element
-- coercing `Map k v` to `Map k v'`
-- >>> coerce (singleton 'S' True ) ∷ Map Char (Reverse Bool)
-- fromList [('S',Reverse {getReverse = True})]

-- coercing `Map k v` to `Map k' v`
-- >>> coerce (singleton 'S' True ) ∷ Map (Reverse Bool) Char
-- Couldn't match type `Char' with `Reverse Bool' arising from a use of `coerce' ...

---------------
-- 8.2 Roles --
---------------

-- What differentiates k from v in `Map k v`?
-- Their roles are different.
-- Just as the type system ensures terms are used correctly,
-- and the kind system ensures types are logical,
-- THE ROLE SYSTEM ENSURES COERCIONS ARE SAFE.

-- Every type parameter for a given type constructor is assigned a role.
-- PHANTOM:          Two types are always phantomly equal to one another.
-- REPRESENTATIONAL: Types `a` and `b` are representationally equal iff it’s safe to reinterpret the memory of an `a` as a `b`.
-- NOMINAL:          The everyday notion of type-equality, corresponding to the `a ∼ b` constraint. E.g. Int is nominally equal only to itself.

-- Examples:
-- 1. The type variable `a` in `data Proxy a = Proxy` is at role PHANTOM. `Coercible (Proxy a) (Proxy b)` is always true.
-- 2. In the newtype `Sum a`, we say that a has the REPRESENTATIONAL role.
-- 3. Coercible (Map k1 v) (Map k2 v)` is only the case when `k1 ∼ k2`. In `Coercible k1 k2` `k` must be at role NOMINAL.
--    This is the only way to make sure there exists an Ord instance.

-- The syntax for role annotations is `type role TypeConstructor role1 role2 ...`,
-- where roles are given for type variables in the same order they're defined.

-- Exercise 8.2-i: What is the role signature of Either a b?
-- type role Either representational representational

-- Exercise 8.2-ii: What is the role signature of Proxy a?
-- type role Proxy phantom

-- There is an inherent ordering in roles:
-- phantom < representational < nominal
-- Upgrading from a weaker role to a stronger one is known as STRENGTHENING.

-- Just like types, roles are automatically inferred by the compiler, though they can be specified explicitly.
-- This inference works as follows:

-- 1. All type parameters are assumed to be at role PHANTOM.
-- 2. The type constructor (→) has two REPRESENTATIONAL roles; any type parameter applied to a (→) gets
--    upgraded to representational. Data constructors count as applying (→).
-- 3. The type constructor (∼) has two NOMINAL roles; any type parameter applied to a (∼) gets upgraded to
--    nominal. GADTs and type families count as applying (∼).

-- Why must types used by type families be at role `nominal`?

-- a type family that replaces Int with Bool (leaves any other type alone)
type family IntToBool a where
  IntToBool Int = Bool
  IntToBool a = a

-- Is it safe to say `a` is at role representational? No!
-- `Coercible a b ⇒ Coercible (IntToBool a) (IntToBool b)` doesn't hold in general.
-- In particular, it fails whenever `a ∼ Int`.

-- It's possible to strengthen an inferred role to a less permissive one by providing a role signature.

-- Binary search trees (like Maps) have an implicit memory dependency on their Ord instance.
data BST v = Empty | Branch !(BST v) !v !(BST v)

-- Roles are given for type variables in the same order they're defined.
-- type role TypeConstructor role1 role2 ...
-- type role BST phantom ----------- weakening not allowed
-- type role BST representational -- this is the role the role system found out
-- type role BST nominal ----------- strengthening allowed

-- It's only possible to STRENGTHEN inferred roles.
-- type role BST phantom
-- Compiler error: "Role mismatch on variable v: Annotation says phantom but role representational is required."
