{-# LANGUAGE UnicodeSyntax #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}

--------------------------
-- Chapter 13: Generics --
--------------------------

-- 13.1 Generic Representations
-- 13.2 Deriving Structural Polymorphism
-- 13.3 Using Generic Metadata
-- 13.4 Performance
-- 13.5 Kan Extensions

module Kan where

import Control.Monad.Codensity
import Data.Functor.Day.Curried
import Data.Functor.Yoneda

-------------------------
-- 13.5 Kan Extensions --
-------------------------

{-

Yoneda, Curried and Codensity all come from the kan-extensions package, e.g.

newtype Yoneda f a = Yoneda { runYoneda ∷ ∀ b. (a → b) → f b }

Note the lack of a `Functor f` constraint on this instance!
`Yoneda f` is a Functor even when f isn't.
In essence, `Yoneda f` gives us a instance of Functor for free.

instance Functor (Yoneda f) where
  fmap f (Yoneda y) = Yoneda (\k → y (k . f))

How does Yoneda help GHC optimize our programs?
GHC's failure to inline "too polymorphic" functions is due to it being unable to perform the functor/etc. laws while inlining polymorphic code.
But `Yoneda f` is a functor even when `f` isn't - exactly by implementing the Functor laws by hand.
Yoneda's Functor instance can't possibly depend on f.
That means `Yoneda f` is never "too polymorphic" and as a result, acts as a fantastic carrier for optimization.

The functions `liftYoneda ∷ Functor f ⇒ f a → Yoneda f a` and `lowerYoneda ∷ Yoneda f a → f a`
witness an isomorphism between `Yoneda f a` and `f a`.
Whenever your generic code needs to do something in f it should use liftYoneda,
and the final interface to your generic code should make a call to lowerYoneda to hide it as an implementation detail.
This argument holds exactly when replacing Functor with Applicative or Monad, and Yoneda with Curried or Codensity respectively.

-}

------------------------------------
-- Yoneda and Functor are similar --
------------------------------------

-- >>> :type runYoneda
-- runYoneda ∷ Yoneda f a → ∀ b. (a → b) → f b
-- flip fmap ∷ Functor f ⇒ f a → (a → b) → f b

-- >>> :type flip fmap
-- flip fmap ∷ Functor f ⇒ f a → (a → b) → f b

-------------------------------------
-- Codensity and Monad are similar --
-------------------------------------

-- >>> :type runCodensity
-- runCodensity
--   ∷ ∀ k (m ∷ k → *) a.
--      Codensity m a → ∀ (b ∷ k). (a → m b) → m b

-- >>> :type (>>=)
-- (>>=) ∷ Monad m ⇒ m a → (a → m b) → m b

-----------------------------------------
-- Curried and Applicative are similar --
-----------------------------------------

-- >>> :type runCurried @(Yoneda _) @(Yoneda _)
-- runCurried @(Yoneda _) @(Yoneda _)
--   ∷ Curried (Yoneda w1) (Yoneda w2) a
--      → ∀ r. Yoneda w1 (a → r) → Yoneda w2 r

-- >>> :type flip (<*>)
-- flip (<*>) ∷ Applicative f ⇒ f a → f (a → b) → f b

-- Cookbook recipe:
-- Rewrite too-polymorphic generic code in terms of kan extensions.
-- - ∀ f. Functor     f ⇒ f a ⇒ ∀ f. Yoneda f a
-- - ∀ f. Applicative f ⇒ f a ⇒ ∀ f. Curried (Yoneda f) (Yoneda f) a
-- - ∀ f. Monad       f ⇒ f a ⇒ ∀ f. Codensity f a

