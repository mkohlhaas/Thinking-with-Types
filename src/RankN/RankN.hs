{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

----------------------------
-- Chapter 6: Rank-NTypes --
----------------------------

-- 6.1 Introduction
-- 6.2 Ranks
-- 6.3 The Nitty Gritty Details
-- 6.4 The Continuation Monad

module RankN where

import Control.Monad.Trans.Class (MonadTrans (..))

----------------------
-- 6.1 Introduction --
----------------------

-- A bit of Terminology first:
-- ENDOMORPHISMS are functions which take and return the same type, e.g.
-- not ∷ Bool → Bool
-- show @String ∷ String → String
-- id ∷ a → a

-- Sometimes Haskell's default notion of polymorphism simply isn't polymorphic enough. ;-)

-- Example:
-- We want to write a function which takes 'id ∷ a → a' as an argument (and only `id`), and applies it to the number 5.

-- Compiler Error: "Couldn't match expected type ‘Int’ with actual type ‘a’"
-- applyToFive' ∷ (a → a) → Int
-- applyToFive' ∷ ∀ a. (a → a) → Int -- this is what Haskell actually generated (implicit quantification)
-- applyToFive' f = f 5

-- By default, Haskell will automatically quantify our type variables (IMPLICIT QUANTIFICATION),
-- That means that the type signature 'a → a' is really syntactic sugar for '∀ a. a → a'.

-- The signature '(a → a) → Int' promises that applyToFive will take ANY endomorphism.
-- The choice of `a` is at the mercy of the CALLER.

-- But this is the signature we actually need in applyToFive:
-- id ∷ a → a       -- but Haskell generated actually ...
-- id ∷ ∀ a. a → a  -- ... this. And this is the signature we need in applyToFive'!
-- id a = a

-- By enabling RankNTypes we can write these desugared types explicitly.
--     precisely the signature of `id`
--                  |
applyToFive ∷ (∀ a. a → a) → Int
applyToFive f = f 5

-- as expected this doesn't work (although `not` is an endomorphism and you might have thought it should have worked)
-- >>> applyToFive not
-- Couldn't match type `a' with `Bool' ...

-- works
-- >>> applyToFive id
-- 5

---------------
-- 6.2 Ranks --
---------------

-- The RankNTypes extension allows us to introduce polymorphism anywhere a type is allowed, not only on top-level bindings!
-- The RankNTypes is best thought of as making polymorphism first-class.

-- In type-theory lingo, the rank of a function is the "depth" of its polymorphism.

-- A function that has no polymorphic parameters is    rank 0.
-- Most polymorphic functions you're familiar with are rank 1, e.g. 'const ∷ a → b → a', 'head ∷ [a] → a', ...
-- 'applyToFive' is                                    rank 2, because its first parameter itself is rank 1.

-- Usually we call functions above 'rank-1' to be 'rank-n' or `higher rank`.

-- The intuition behind higher-rank types is that they are functions which take callbacks.
-- The rank of a function is how often control gets "handed off".
-- A rank-2 function will call a polymorphic function for you, while a rank-3 function will run a callback which itself runs a callback ...

-- Caller decides `a`
-- Function `f` is rank-0 because it is no longer polymorphic.
-- The caller of applyToFive' has already instantiated `a` by the time applyToFive' gets access to it.
-- And as such, it's an error to apply it to 5. We have no guarantees that the caller decided `a ∼ Int`.
-- applyToFive' ∷ ∀ a. (a → a) → Int
-- applyToFive' f = f 5

-- Callee decides `a`
-- By pushing up the rank of applyToFive, we can delay who gets to decide the type `a`.
-- We move it from being the caller's choice to being the callee's choice.
-- applyToFive ∷ (∀ a. a → a) → Int
-- applyToFive f = f 5

-- Higher-yet ranks also work in this fashion.
-- The caller of the function and the implementations seesaw between who is responsible for instantiating the polymorphic types.

----------------------------------
-- 6.3 The Nitty Gritty Details --
----------------------------------

-- A function gains higher rank every time a ∀ quantifier exists on the left-side of a function arrow.

-- The rank of a function is simply the number of arrows its deepest ∀ is to the left of.
-- Note: The ∀ quantifier binds more loosely than the arrow type (→).

-- Cookbook recipe:
-- 1. Add implicit parentheses (esp. around (→)).
-- 2. Count number of arrows in deepest ∀.

-- Int → ∀ a. a → a
-- Int → (∀ a. (a → a))
-- (Int → (∀ a. (a → a)))                       -- rank-1
--         |       1
--      deepest ∀

-- ∀ a. a → a
-- ∀ a. (a → a)
-- (∀ a. (a → a))                               -- rank-1
--  |       1
-- deepest ∀

-- ∀ r. ((∀ a. (a → r)) → r)
-- (∀ r. ((∀ a. (a → r)) → r))                  -- rank-2
--  |              1
-- deepest ∀

-- (a → b) → (∀ c. c → a) → b
-- (a → b) → ((∀ c. c → a) → b)
-- ((a → b) → ((∀ c. c → a) → b))               -- rank-2
--              |      1    2
--          deepest ∀

-- ((∀ x. m x → b (z m x)) → b (z m a)) → m a
-- (((∀ x. m x → b (z m x)) → b (z m a)) → m a) -- rank-3
--    |        1            2            3
-- deepest ∀

--------------------------------
-- 6.4 The Continuation Monad --
--------------------------------

-- Types `a` and `∀ r. (a → r) → r` are isomorphic.
-- Intuitively, we understand this as saying that having a value is just as good as having a function that will give that value to a callback.

toCont ∷ a → (∀ r. (a → r) → r)
toCont a f = f a

-- >>> :type toCont True
-- toCont True ∷ (Bool → r) → r

fromCont ∷ (∀ r. (a → r) → r) → a
fromCont c = c id

-- >>> :type fromCont (toCont True)
-- fromCont (toCont True) ∷ Bool

-- >>> fromCont (toCont True)
-- True

-- >>> :type toCont . fromCont
-- Couldn't match expected type `∀ r. (a → r) → r' with actual type `a'

-- >>> :type fromCont . toCont
-- Couldn't match expected type: ∀ r. (c → r) → r with actual type: (a → r) → r

-- `toCont` and `fromCont` are NOT really forming an isomorphism!!!
-- toCont . fromCont ≠ id
-- fromCont . toCont ≠ id

-- runCont means: Give me your "hidden" value `a` (as `id` does not change the value)!
runCont ∷ (∀ r. (a → r) → r) → a
runCont = fromCont

-- The type `∀ r. (a → r) → r` is known as being in continuation-passing style or more tersely as CPS.

-- Isomorphisms are transitive.
-- If we have an isomorphism t1 ≌ t2, and another t2 ≌ t3, we must also have one t1 ≌ t3.

-- Caller: You got the String, but I tell you what to do with it and you return that value to me.
withOS ∷ (String → r) → r
withOS f = f "linux" ------------ "hidden" value: "linux"

-- Caller: You got the Double, but I tell you what to do with it and you return that value to me.
withVersionNumber ∷ (Double → r) → r
withVersionNumber f = f 1.0 ----- "hidden" value: 1.0

-- Caller: You got the Int, but I tell you what to do with it and you return that value to me.
withTimestamp ∷ (Int → r) → r
withTimestamp f = f 1532083362 -- "hidden" value: 1532083362

-- >>> withOS show
-- "\"linux\""

-- just to make the function parameter explicit
-- >>> withOS (\os → show os)
-- "\"linux\""

-- >>> withVersionNumber (\version → show version)
-- "1.0"

-- >>> withTimestamp (\timestamp → show timestamp)
-- "1532083362"

-- >>> runCont withOS
-- "linux"

-- >>> runCont withVersionNumber
-- 1.0

-- >>> runCont withTimestamp
-- 1532083362

-- "pyramid of doom"
releaseString1 ∷ String
releaseString1 =
  withVersionNumber $ \version →
    withTimestamp $ \date →
      withOS $ \os →
        os ++ "-" ++ show version ++ "-" ++ show date

-- >>> releaseString1
-- "linux-1.0-1532083362"

-- another "pyramid of doom"
releaseString2 ∷ String
releaseString2 =
  withOS $ \os →
    withTimestamp $ \date →
      withVersionNumber $ \version →
        os ++ "-" ++ show version ++ "-" ++ show date

-- >>> releaseString2
-- "linux-1.0-1532083362"

-- Since we know that `Identity a ≌ a` and that `a ≌ ∀ r. (a → r) → r`, we should expect the transitive isomorphism between `Identity a` and CPS.
-- Since we know that Identity a is a Monad and that isomorphisms preserve typeclasses, we should expect that CPS also forms a Monad.

newtype Cont r a = Cont {unCont ∷ (a → r) → r}

-- >>> fromCont withOS
-- "linux"

-- the same
-- >>> runCont $ unCont $ Cont withOS
-- "linux"

-- >>> :info Functor
-- type Functor ∷ (* → *) → Constraint
-- class Functor f where
--   fmap ∷ (a → b) → f a → f b
--   (<$) ∷ a → f b → f a
--   {-# MINIMAL fmap #-}

instance Functor (Cont r) where
  fmap ∷ (a → b) → Cont r a → Cont r b
  fmap f (Cont c) = Cont $ \g → c (g . f)

-- >>> :info Applicative
-- type Applicative ∷ (* → *) → Constraint
-- class Functor f ⇒ Applicative f where
--   pure ∷ a → f a
--   (<*>) ∷ f (a → b) → f a → f b
--   liftA2 ∷ (a → b → c) → f a → f b → f c
--   {-# MINIMAL pure, ((<*>) | liftA2) #-}

instance Applicative (Cont r) where
  pure ∷ a → Cont r a
  pure a = Cont $ \f → f a
  (<*>) ∷ Cont r (a → b) → Cont r a → Cont r b
  Cont f <*> Cont a = Cont $ \g → f (\h → a (g . h))

-- >>> :info Monad
-- type Monad ∷ (* → *) → Constraint
-- class Applicative m ⇒ Monad m where
--   (>>=) ∷ m a → (a → m b) → m b
--   {-# MINIMAL (>>=) #-}

instance Monad (Cont r) where
  (>>=) ∷ Cont r a → (a → Cont r b) → Cont r b
  Cont a >>= f = Cont $ \g → a (\h → unCont (f h) g)

releaseStringCont ∷ String
releaseStringCont = runCont $ unCont $ do
  os ← Cont withOS
  version ← Cont withVersionNumber
  date ← Cont withTimestamp
  pure $ os ++ "-" ++ show version ++ "-" ++ show date

-- >>> releaseStringCont
-- "linux-1.0-1532083362"

-- There is also a monad transformer version of Cont.
-- The Functor, Applicative and Monad instances for ContT are identical to Cont.
newtype ContT m a = ContT {unContT ∷ ∀ r. (a → m r) → m r}

instance Functor (ContT m) where
  fmap ∷ (a → b) → ContT m a → ContT m b
  fmap f (ContT c) = ContT $ \g → c (g . f)

instance Applicative (ContT m) where
  pure ∷ a → ContT m a
  pure a = ContT $ \f → f a
  (<*>) ∷ ContT m (a → b) → ContT m a → ContT m b
  ContT f <*> ContT a = ContT $ \g → f (\h → a (g . h))

instance Monad (ContT m) where
  (>>=) ∷ ContT m a → (a → ContT m b) → ContT m b
  ContT a >>= f = ContT $ \g → a (\h → unContT (f h) g)

-- >>> :info MonadTrans
-- type MonadTrans ∷ ((* → *) → * → *) → Constraint
-- class MonadTrans t where
--   lift ∷ Monad m ⇒ m a → t m a
--   {-# MINIMAL lift #-}

instance MonadTrans ContT where
  lift ∷ Monad m ⇒ m a → ContT m a
  lift m = ContT (m >>=)
