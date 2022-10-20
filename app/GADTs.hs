{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS -Wall #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module GADTs where -- pronounced "gad-its"

import Data.Kind (Constraint, Type)

---------------------------
-- Type Safe Syntax Tree --
---------------------------

-- Generalized algebraic datatypes are an extension to Haskell's type system
-- that allow explicit type signatures to be written for data constructors.
data Expr a where
  LitInt ∷ Int → Expr Int
  LitBool ∷ Bool → Expr Bool
  Add ∷ Expr Int → Expr Int → Expr Int
  Not ∷ Expr Bool → Expr Bool
  If ∷ Expr Bool → Expr a → Expr a → Expr a

-- Expr is correct by construction.
-- We are incapable of building a poorly-typed Expr.
-- E.g. we're unable to build an AST which attempts to add an Expr Int to a Expr Bool.

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

-- GADTs allow us to specify a data constructor's type, we can use them to constrain a type variable.
-- Haskell can use the knowledge of these constrained types.
-- We can use this to write a typesafe evaluator over Expr.
evalExpr ∷ Expr a → a
evalExpr (LitInt i) = i -- returns an Int
evalExpr (LitBool b) = b -- returns a Bool - this is possible because Haskell can reason about GADTs
evalExpr (Add x y) = evalExpr x + evalExpr y
evalExpr (Not x) = not $ evalExpr x
evalExpr (If b x y) = if evalExpr b then evalExpr x else evalExpr y

-- GADTs are merely syntactic sugar over type equalities.

-- traditional Haskell datatype
-- Each data constructor of Expr_ carries along with it a type equality constraint.
-- Like any constraint inside a data constructor, Haskell will require the constraint to be proven when the data constructor is called.
data Expr_ a
  = (a ~ Int) ⇒ LitInt_ Int
  | (a ~ Bool) ⇒ LitBool_ Bool
  | (a ~ Int) ⇒ Add_ (Expr_ Int) (Expr_ Int)
  | (a ~ Bool) ⇒ Not_ (Expr_ Bool)
  | If_ (Expr_ Bool) (Expr_ a) (Expr_ a)

-- >>> :type evalExpr_
-- evalExpr_ ∷ Expr_ a → a

-- >>> evalExpr_ (LitInt_ 13)
-- 13

-- >>> evalExpr_ . Not_ $ LitBool_ True
-- False

-- >>> evalExpr_ $ If_ (LitBool_ True) (LitInt_ 1) (Add_ (LitInt_ 5) (LitInt_ 13))
-- 1

-- >>> evalExpr_ $ If_ (LitBool_ False) (LitInt_ 1) (Add_ (LitInt_ 5) (LitInt_ 13))
-- 18

evalExpr_ ∷ Expr_ a → a
evalExpr_ (LitInt_ i) = i
evalExpr_ (LitBool_ b) = b
evalExpr_ (Add_ x y) = evalExpr_ x + evalExpr_ y
evalExpr_ (Not_ x) = not $ evalExpr_ x
evalExpr_ (If_ b x y) = if evalExpr_ b then evalExpr_ x else evalExpr_ y

-------------------------
-- Heterogeneous Lists --
-------------------------

-- One of the primary motivations of GADTs is building inductive type-level structures out of term-level data.
data HList (ts ∷ [Type]) where -- kind signature: `ts` is defined to have kind `[Type]`
  HNil ∷ HList '[] -- empty list of types
  (:#) ∷ t → HList ts → HList (t ': ts) -- symbolically named data constructors in Haskell must begin with a leading colon

infixr 5 :#

-- >>> :type HNil
-- HNil ∷ HList '[]

-- >>> :t True :# HNil
-- True :# HNil ∷ HList '[Bool]

-- >>> let hlist = Just "hello" :# True :# HNil
-- >>> :type hlist
-- >>> hLength hlist
-- hlist ∷ HList '[Maybe String, Bool]
-- 2

-- >>> let hlist = Just "hello" :# True :# HNil
-- >>> hHead hlist
-- Just "hello"

-- >>> Just "hello" :# True :# "again":# HNil
-- Just "hello" :# True :# "again" :# HNil

-- >>> let hlist = Just "hello" :# True :# "again":# HNil
-- >>> showBool hlist
-- "True"

-- >>> let hlist = Just "hello" :# True :# HNil
-- >>> showBool hlist
-- Couldn't match type: '[]
--                with: '[b0_a2JGD[tau:1]]
-- Expected: HList '[Maybe String, Bool, b0_a2JGD[tau:1]]
--   Actual: HList '[Maybe String, Bool]
-- In the first argument of `showBool', namely `hlist'
-- In the expression: showBool hlist
-- In an equation for `it_a2JFF': it_a2JFF = showBool hlist

-- Using the manually written Show instance.
-- >>> Just "hello" :# True :# "again":# HNil
-- Just "hello" :# True :# "again" :# HNil

-- Using the manually written Eq instance.
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

-- HList can be pattern matched over.
-- A total head function - something impossible to do with traditional lists.
hHead ∷ HList (t ': ts) → t
hHead (t :# _) = t

showBool ∷ HList '[a, Bool, b] → String
showBool (_ :# b :# _ :# HNil) = show b

hLength ∷ HList ts → Int
hLength HNil = 0
hLength (_ :# ts) = 1 + hLength ts

-- Unfortunately, GHC's stock deriving machinery doesn't play nicely with GADTs.
-- It will refuse to write Eq, Show or other instances.

{-

-- # eqHNil
instance Eq (HList '[]) where
  (==) ∷ HList '[] → HList '[] → Bool
  HNil == HNil = True

-- # eqHCons
instance (Eq t, Eq (HList ts)) ⇒ Eq (HList (t ': ts)) where
  (==) ∷ (Eq t, Eq (HList ts)) ⇒ HList (t : ts) → HList (t : ts) → Bool
  (a :# as) == (b :# bs) = a == b && as == bs

-- # ordHNil
instance Ord (HList '[]) where
  compare ∷ HList '[] → HList '[] → Ordering
  compare HNil HNil = EQ

-- # ordHCons
instance (Ord t, Ord (HList ts)) ⇒ Ord (HList (t ': ts)) where
  compare ∷ (Ord t, Ord (HList ts)) ⇒ HList (t : ts) → HList (t : ts) → Ordering
  compare (a :# as) (b :# bs) = compare a b <> compare as bs

-- # showHNil
instance Show (HList '[]) where
  show ∷ HList '[] → String
  show HNil = "HNil"

-- # showHCons
instance (Show t, Show (HList ts)) ⇒ Show (HList (t ': ts)) where
  show ∷ (Show t, Show (HList ts)) ⇒ HList (t : ts) → String
  show (a :# as) = show a <> " :# " <> show as

-}

-- {-

-- We can write a closed type family which will fold ts into one big CONSTRAINT stating each element has an Eq.
type family AllEq (ts ∷ [Type]) ∷ Constraint where
  AllEq '[] = ()
  AllEq (t ': ts) = (Eq t, AllEq ts)

-- There is nothing specific to Eq about AllEq.
-- It can be generalized into a fold over any CONSTRAINT c.
-- type family All (c ∷ Type → Constraint) (ts ∷ [Type]) ∷ Constraint where
type All ∷ (Type → Constraint) → [Type] → Constraint
type family All c ts where
  All c '[] = () -- unit constraint/empty constraint
  All c (t ': ts) = (c t, All c ts)

-- # eqHList
instance All Eq ts ⇒ Eq (HList ts) where
  (==) ∷ All Eq ts ⇒ HList ts → HList ts → Bool
  HNil == HNil = True
  (a :# as) == (b :# bs) = a == b && as == bs

-- # ordHList
instance (All Eq ts, All Ord ts) ⇒ Ord (HList ts) where
  compare ∷ (All Eq ts, All Ord ts) ⇒ HList ts → HList ts → Ordering
  compare HNil HNil = EQ
  compare (a :# as) (b :# bs) = compare a b <> compare as bs

-- # showHList
instance (All Show ts) ⇒ Show (HList ts) where
  show ∷ All Show ts ⇒ HList ts → String
  show HNil = "HNil"
  show (a :# as) = show a <> " :# " <> show as

-- -}

-- creates a nested pair of constraints which Haskell accepts as a constraint
-- >>> :kind! AllEq '[Int , Bool, String, Int]
-- AllEq '[Int , Bool, String, Int] ∷ Constraint
-- = (Eq Int, (Eq Bool, (Eq [Char], (Eq Int, () ∷ Constraint))))

-- foldHList ∷ ∀ c ts m . (All c ts, Monoid m) ⇒ (∀ t. c t ⇒ t → m) → HList ts → m
-- foldHList _ HNil = mempty
-- foldHList f (a :# as) = f a <> foldHList @c f as
