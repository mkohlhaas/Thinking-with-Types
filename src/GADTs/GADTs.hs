{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Unused LANGUAGE pragma" #-}

--------------------------------------
-- Chapter 5: Constraints and GADTs --
--------------------------------------

-- 5.1 Introduction
-- 5.2 GADTs
-- 5.3 Heterogeneous Lists

module GADTs where -- pronounced "gad-its"

import Data.Kind (Constraint, Type)

----------------------
-- 5.1 Introduction --
----------------------

-- The CONSTRAINT kind is reserved for things that can appear on the left side of the fat context arrow (⇒).
-- This includes:
-- 1. Fully saturated typeclasses, e.g. `Show a`,
-- 2. Tuples of constraints      , e.g. `(Show a, Eq a)`
-- 3. Type equalities,           , e.g. `(Int ∼ a.)`

-- Type equalities form an equivalence relation.
-- 1. Reflexivity:  a type is always equal to itself, a ∼ a.
-- 2. Symmetry:     a ∼ b holds if and only if b ∼ a
-- 3. Transitivity: if a ∼ b and b ∼ c then a ∼ c.

-- For Haskell `five` and `five'` are identical.
-- While `five` has type Int, `five'` has type `a`, along with a constraint saying that `a` equals Int.

five ∷ Int
five = 5

five' ∷ (a ~ Int) ⇒ a
five' = 5

-- Tuples of constraints can be their own constraint.
type ShowAndNum a = (Show a, Num a)

-- >>> :kind! ShowAndNum
-- ShowAndNum ∷ * → Constraint
-- = ShowAndNum

-- >>> :kind! ShowAndNum Int
-- ShowAndNum Int ∷ Constraint
-- = (Show Int, Num Int)

-- same
-- class (Show a, Num a) ⇒ ShowNum a
class ShowAndNum a ⇒ ShowNum a

-- same
-- instance (Show a, Num a) ⇒ ShowNum a
instance ShowAndNum a ⇒ ShowNum a

---------------
-- 5.2 GADTs --
---------------

-- Generalized algebraic datatypes are an extension to Haskell's type system
-- that allow explicit type signatures to be written for data constructors.

-- The canonical example of a GADT is a TYPE SAFE SYNTAX TREE.

-- 1. Standard Haskell Datatype
-- Activate it to see type errors pop up in `evalExpr`!
-- data Expr a
--   = LitInt Int
--   | LitBool Bool
--   | Add (Expr Int) (Expr Int)
--   | Not (Expr Bool)
--   | If (Expr Bool) (Expr a) (Expr a)

-- 2. Type Equalities

-- Each data constructor of `Expr` carries along with it a type equality constraint.
-- Like any constraint inside a data constructor, Haskell will require the constraint to be proven when the data constructor is called.
-- In other words Haskell can reason about type equalities and `evaExpr` works again!
-- No type errors in `evalExpr`!
-- data Expr a
--   = (a ~ Int) ⇒ LitInt Int
--   | (a ~ Bool) ⇒ LitBool Bool
--   | (a ~ Int) ⇒ Add (Expr Int) (Expr Int)
--   | (a ~ Bool) ⇒ Not (Expr Bool)
--   | If (Expr Bool) (Expr a) (Expr a)

-- 3. GADT

-- GADTs are merely syntactic sugar over type equalities!

-- No type errors in `evalExpr`!
data Expr a where -- "where" turns on GADT syntax
  LitInt ∷ Int → Expr Int
  LitBool ∷ Bool → Expr Bool
  Add ∷ Expr Int → Expr Int → Expr Int
  Not ∷ Expr Bool → Expr Bool
  If ∷ Expr Bool → Expr a → Expr a → Expr a

-- >>> :type LitInt
-- LitInt ∷ Int → Expr Int

-- >>> :type If
-- If ∷ Expr Bool → Expr a → Expr a → Expr a

-- >>> :type evalExpr
-- evalExpr ∷ Expr a → a

-- >>> evalExpr (LitInt 13)
-- 13

-- >>> evalExpr . Not $ LitBool True
-- False

-- >>> evalExpr $ If (LitBool True) (LitInt 1) (Add (LitInt 5) (LitInt 13))
-- 1

-- >>> evalExpr $ If (LitBool False) (LitInt 1) (Add (LitInt 5) (LitInt 13))
-- 18

-- typesafe evaluator over Expr
evalExpr ∷ Expr a → a
evalExpr (LitInt i) = i --- returns an Int!
evalExpr (LitBool b) = b -- returns a Bool! ⇒ This is possible because Haskell can reason about GADTs and type equalities but not about normal data definitions!!!
evalExpr (Add x y) = evalExpr x + evalExpr y
evalExpr (Not x) = not $ evalExpr x
evalExpr (If b x y) = if evalExpr b then evalExpr x else evalExpr y

-----------------------------
-- 5.3 Heterogeneous Lists --
-----------------------------

-- GADTs can be used to BUILD INDUCTIVE TYPE-LEVEL STRUCTURES out of term-level data!

data HList (ts ∷ [Type]) where ----------- kind signature: `ts` is defined to have kind `[Type]`
  HNil ∷ HList '[] ----------------------- empty list of types
  (:#) ∷ t → HList ts → HList (t ': ts) -- symbolically named data constructors in Haskell must begin with a leading colon

infixr 5 :#

----------------------------------
-- Creating Heterogeneous Lists --
----------------------------------

-- >>> :type True :# HNil
-- True :# HNil ∷ HList '[Bool]

-- >>> :type Just "hello" :# True :# HNil
-- Just "hello" :# True :# HNil ∷ HList '[Maybe String, Bool]

----------------------------------------------
-- Pattern Matching on a Heterogeneous List --
----------------------------------------------

-- >>> hHead $ Just "hello" :# True :# HNil
-- Just "hello"

-- doesn't compile
-- >>> hHead HNil
-- Couldn't match type: '[] with: t_a82RT[sk:1] : ts0_a82RU[tau:1]

-- pattern matches
-- >>> showBool $ Just "hello" :# True :# "again":# HNil
-- "True"

-- doesn't pattern match
-- >>> showBool $ Just "hello" :# True :# HNil
-- Couldn't match type: '[]

-----------------------------
-- Using the Show Instance --
-----------------------------

-- >>> Just "hello" :# True :# "again":# HNil
-- Just "hello" :# True :# "again" :# HNil

-- >>> Just "hello" :# True :# "again":# HNil
-- Just "hello" :# True :# "again" :# HNil

---------------------------
-- Using the Eq Instance --
---------------------------

-- >>> HNil == HNil
-- True

-- >>> let hlist1 = Just "hello" :# True :# HNil
-- >>> let hlist2 = Just "hello" :# True :# HNil
-- >>> hlist1 == hlist2
-- True

-- >>> let hlist1 = Just "hello" :# True :# HNil
-- >>> let hlist2 = Just "again" :# False :# HNil
-- >>> hlist1 == hlist2
-- False

----------------------------
-- Using the Ord Instance --
----------------------------

-- >>> let hlist1 = Just "hello" :# True :# HNil
-- >>> let hlist2 = Just "hello" :# True :# HNil
-- >>> compare hlist1 hlist2
-- EQ

-- >>> let hlist1 = Just "hello" :# True :# HNil
-- >>> let hlist2 = Just "again" :# False :# HNil
-- >>> compare hlist1 hlist2
-- GT

-- >>> let hlist1 = Just "hello" :# True :# HNil
-- >>> let hlist2 = Just "again" :# False :# HNil
-- >>> compare hlist2 hlist1
-- LT

-- both lists must be of the same type
-- >>> let hlist1 = Just "hello" :# True :# "hello" :# HNil
-- >>> let hlist2 = Just "again" :# False :# HNil
-- >>> compare hlist2 hlist1
-- Couldn't match type: '[String] with: '[]

-- HList can be pattern matched over.
-- A total head function - something impossible to do with traditional lists.
hHead ∷ HList (t ': ts) → t
hHead (t :# _) = t

showBool ∷ HList '[a, Bool, b] → String
showBool (_ :# b :# _ :# HNil) = show b

hLength ∷ HList ts → Int
hLength HNil = 0
hLength (_ :# ts) = 1 + hLength ts

-----------------------------------
-- 1. Manually Writing Instances --
-----------------------------------

{-

-- Unfortunately, GHC's stock deriving machinery doesn't play nicely with GADTs.
-- It will refuse to write Eq, Show and other instances.

----------------------------
-- Eq instances for HList --
----------------------------

instance Eq (HList '[]) where
  (==) ∷ HList '[] → HList '[] → Bool
  HNil == HNil = True

instance (Eq t, Eq (HList ts)) ⇒ Eq (HList (t ': ts)) where
  (==) ∷ (Eq t, Eq (HList ts)) ⇒ HList (t : ts) → HList (t : ts) → Bool
  (a :# as) == (b :# bs) = a == b && as == bs

-----------------------------
-- Ord instances for HList --
-----------------------------

instance Ord (HList '[]) where
  compare ∷ HList '[] → HList '[] → Ordering
  compare HNil HNil = EQ

instance (Ord t, Ord (HList ts)) ⇒ Ord (HList (t ': ts)) where
  compare ∷ (Ord t, Ord (HList ts)) ⇒ HList (t : ts) → HList (t : ts) → Ordering
  compare (a :# as) (b :# bs) = compare a b <> compare as bs

------------------------------
-- Show instances for HList --
------------------------------

instance Show (HList '[]) where
  show ∷ HList '[] → String
  show HNil = "HNil"

instance (Show t, Show (HList ts)) ⇒ Show (HList (t ': ts)) where
  show ∷ (Show t, Show (HList ts)) ⇒ HList (t : ts) → String
  show (a :# as) = show a <> " :# " <> show as

-}

---------------------------------------------------------
-- 2. Using a Closed Type Family for Writing Instances --
---------------------------------------------------------

-- {-

-- We can write a closed type family which will fold `ts` into one big CONSTRAINT stating each element has an Eq.
type family AllEq (ts ∷ [Type]) ∷ Constraint where
  AllEq '[] = () ---------------------- unit constraint/empty constraint
  AllEq (t ': ts) = (Eq t, AllEq ts) -- creates a pair of pairs of pairs ... of Constraints

-- >>> :kind! (AllEq '[Int, Bool, String])
-- (AllEq '[Int, Bool, String]) ∷ Constraint
-- = (Eq Int, (Eq Bool, (Eq [Char], () ∷ Constraint)))

-- >>> :kind Eq
-- Eq ∷ Type → Constraint

-- >>> :kind Eq
-- Eq ∷ Type → Constraint

-- >>> :kind Show
-- Show ∷ Type → Constraint

-- generalizing for any Constraint
-- type family All (f ∷ Type → Constraint) (ts ∷ [Type]) ∷ Constraint where
type All ∷ (Type → Constraint) → [Type] → Constraint
type family All f ts where
  All f '[] = () --------------------- unit constraint/empty constraint
  All f (t ': ts) = (f t, All f ts) -- creates a pair of pairs of pairs ... of Constraints

-- >>> :kind! All Show '[]
-- All Show '[] ∷ Constraint
-- = () ∷ Constraint

-- >>> :kind! All Show '[Int, Bool, String]
-- All Show '[Int, Bool, String] ∷ Constraint
-- = (Show Int, (Show Bool, (Show [Char], () ∷ Constraint)))

-- >>> :kind! All Eq '[Int, Bool, String]
-- All Eq '[Int, Bool, String] ∷ Constraint
-- = (Eq Int, (Eq Bool, (Eq [Char], () ∷ Constraint)))

-- creates a nested pair of constraints which Haskell accepts as a constraint
-- >>> :kind! AllEq '[Int , Bool, String, Int]
-- AllEq '[Int , Bool, String, Int] ∷ Constraint
-- = (Eq Int, (Eq Bool, (Eq [Char], (Eq Int, () ∷ Constraint))))

----------------------------
-- Eq instances for HList --
----------------------------
instance All Eq ts ⇒ Eq (HList ts) where
  (==) ∷ All Eq ts ⇒ HList ts → HList ts → Bool
  HNil == HNil = True
  (a :# as) == (b :# bs) = a == b && as == bs

-----------------------------
-- Ord instances for HList --
-----------------------------
instance (All Eq ts, All Ord ts) ⇒ Ord (HList ts) where
  compare ∷ (All Eq ts, All Ord ts) ⇒ HList ts → HList ts → Ordering
  compare HNil HNil = EQ
  compare (a :# as) (b :# bs) = compare a b <> compare as bs

------------------------------
-- Show instances for HList --
------------------------------
instance (All Show ts) ⇒ Show (HList ts) where
  show ∷ All Show ts ⇒ HList ts → String
  show HNil = "HNil"
  show (a :# as) = show a <> " :# " <> show as

-- -}
