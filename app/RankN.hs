{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module RankN where

import Control.Monad.Trans.Class (MonadTrans (..))
import Data.Foldable (asum)
import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Typeable (Typeable, cast, typeRep)

-- import Prelude hiding (id)

-- We want to write a function which takes 'id ∷ a → a' as an argument, and applies it to the number 5.
-- But the signature '(a → a) → Int' promises that applyToFive will take ANY endomorphism.
-- The choice of `a` is at the mercy of the CALLER.
-- "Couldn't match expected type ‘Int’ with actual type ‘a’"
-- applyToFive' ∷ (a → a) → Int
-- applyToFive' f = f 5

-- Endomorphisms are functions which take and return the same type.
-- E.g. 'not ∷ Bool → Bool', 'show @String ∷ String → String' and 'id ∷ a → a' are all endomorphisms.

-- By default, Haskell will automatically quantify our type variables (implicit quantification),
-- meaning that the type signature 'a → a' is really syntactic sugar for '∀ a. a → a'.
-- This is what Haskell actually generated: applyToFive' ∷ ∀ a. (a → a) → Int
-- By enabling RankNTypes we can write these desugared types explicitly.
applyToFive ∷ (∀ a. a → a) → Int -- the ∀ a is now INSIDE parentheses
applyToFive f = f 5

-- this is the signatur we need in applyToFive
-- id ∷ ∀ a. a → a
-- id a = a

-- >>> applyToFive not
-- Couldn't match type `a_a1qVI[sk:2]' with `Bool'

-- >>> applyToFive id
-- 5

-- RankNTypes allows us to introduce polymorphism anywhere a type is allowed, rather than only on top-level bindings.
-- In type-theory lingo, the rank of a function is the "DEPTH" of its polymorphism.

-- A function that has no polymorphic parameters is    rank 0.
-- Most polymorphic functions you're familiar with are rank 1, e.g. 'const ∷ a → b → a', 'head ∷ [a] → a', ...
-- 'applyToFive' is                                    rank 2, because its first parameter itself is rank 1.

-- Usually we call functions above 'rank-1' to be 'rank-n' or higher rank.

-- The intuition behind higher-rank types is that they are functions which take callbacks.
-- The rank of a function is how often control gets "handed off".
-- A rank-2 function will call a polymorphic function for you, while a rank-3 function will run a callback which itself runs a callback.

-- caller decides `a`
-- `f` is rank-0 because it is no longer polymorphic.
-- The caller of applyToFive' has already instantiated `a` by the time applyToFive' gets access to it.
-- And as such, it's an error to apply it to 5. We have no guarantees that the caller decided `a ∼ Int`.
-- applyToFive' ∷ ∀ a. (a → a) → Int
-- applyToFive' f = f 5

-- callee decides `a`
-- By pushing up the rank of applyToFive, we can delay who gets to decide the type `a`.
-- We move it from being the caller's choice to being the callee's choice.
-- applyToFive ∷ (∀ a. a → a) → Int
-- applyToFive f = f 5

-- Even higher-yet ranks also work in this fashion.
-- The caller of the function and the implementations seesaw between who is responsible for instantiating the polymorphic types.

-- A function gains higher rank every time a ∀ quantifier exists on the left-side of a function arrow.

-- The rank of a function is simply the number of arrows its deepest ∀ is to the left of.
-- The ∀ quantifier binds more loosely than the arrow type (→).
-- Cookbook recipe:
-- 1. Add implicit parentheses (esp. around (→)).
-- 2. Count number of arrows in deepest ∀.

-- Int → ∀ a. a → a
-- Int → (∀ a. (a → a))
-- (Int → (∀ a. (a → a)))                       -- rank-1

-- ∀ a. a → a
-- ∀ a. (a → a)
-- (∀ a. (a → a))                               -- rank-1

-- ∀ r. ((∀ a. (a → r)) → r)
-- (∀ r. ((∀ a. (a → r)) → r))                  -- rank-2

-- (a → b) → (∀ c. c → a) → b
-- (a → b) → ((∀ c. c → a) → b)
-- ((a → b) → ((∀ c. c → a) → b))               -- rank-2

-- ((∀ x. m x → b (z m x)) → b (z m a)) → m a
-- (((∀ x. m x → b (z m x)) → b (z m a)) → m a) -- rank-3

-- Types `a` and `∀ r. (a → r) → r` are isomorphic.
-- Intuitively, we understand this as saying that having a value is just as good as having a function that will give that value to a callback.

toCont ∷ a → (∀ r. (a → r) → r)
toCont a f = f a

-- c ≌ continuation
-- fromCont ∷ (∀ r. (a → r) → r) → a
-- fromCont ∷ ((a → a) → t) → t
-- fromCont c =
--  let callback = id
--    in c callback

fromCont ∷ (∀ r. (a → r) → r) → a
fromCont c = c id

-- toCont . fromCont == id
-- fromCont . toCont == id

-- runCont means: Give me your "hidden" value a (as `id` does not change the value)!
runCont ∷ (∀ r. (a → r) → r) → a
runCont = fromCont

-- The type `∀ r. (a → r) → r` is known as being in continuation-passing style or more tersely as CPS.

-- Isomorphisms are transitive.
-- If we have an isomorphism t1 ≌ t2, and another t2 ≌ t3, we must also have one t1 ≌ t3.

-- Caller: You got the Double, but I tell you what to do with it and you return that value to me.
withVersionNumber ∷ (Double → r) → r
withVersionNumber f = f 1.0 -- "hidden" value: 1.0

-- Caller: You got the Int, but I tell you what to do with it and you return that value to me.
withTimestamp ∷ (Int → r) → r
withTimestamp f = f 1532083362 -- "hidden" value: 1532083362

-- Caller: You got the String, but I tell you what to do with it and you return that value to me.
withOS ∷ (String → r) → r
withOS f = f "linux" -- "hidden" value: "linux"

-- >>> withVersionNumber (\version → show version)
-- "1.0"

-- >>> withTimestamp (\timestamp → show timestamp)
-- "1532083362"

-- >>> withOS (\os → show os)
-- "\"linux\""

-- >>> runCont withVersionNumber
-- 1.0

-- >>> runCont withTimestamp
-- 1532083362

-- >>> runCont withOS
-- "linux"

-- "pyramid of doom"
releaseString ∷ String
releaseString =
  withVersionNumber $ \version →
    withTimestamp $ \date →
      withOS $ \os →
        os ++ "-" ++ show version ++ "-" ++ show date

-- >>> releaseString
-- "linux-1.0-1532083362"

-- Since we know that `Identity a ≌ a` and that `a ≌ ∀ r. (a → r) → r`, we should expect the transitive isomorphism between `Identity a` and CPS.
-- Since we know that Identity a is a Monad and that isomorphisms preserve typeclasses, we should expect that CPS also forms a Monad.

newtype Cont r a = Cont {unCont ∷ (a → r) → r}

-- >>> runCont $ unCont $ Cont withOS
-- "linux"

-- fromCont c = c id
-- toCont a f = f a

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
  pure = Cont . toCont

  (<*>) ∷ Cont r (a → b) → Cont r a → Cont r b
  (<*>) (Cont f) (Cont x) = Cont $ \g → f (\h → x (g . h))

-- >>> :info Monad
-- type Monad ∷ (* → *) → Constraint
-- class Applicative m ⇒ Monad m where
--   (>>=) ∷ m a → (a → m b) → m b
--   {-# MINIMAL (>>=) #-}

instance Monad (Cont r) where
  (>>=) ∷ Cont r a → (a → Cont r b) → Cont r b
  (Cont c) >>= f = Cont (\g → c (\x → unCont (f x) g))

releaseStringCont ∷ String
releaseStringCont = runCont $ unCont $ do
  version ← Cont withVersionNumber
  date ← Cont withTimestamp
  os ← Cont withOS
  pure $ os ++ "-" ++ show version ++ "-" ++ show date

-- >>> releaseStringCont
-- "linux-1.0-1532083362"

-- When written in CPS releaseStringCont hides the fact that it's doing nested callbacks.
releaseStringCodensity ∷ String
releaseStringCodensity = fromCont $
  runCodensity $ do
    version ← Codensity withVersionNumber
    date ← Codensity withTimestamp
    os ← Codensity withOS
    pure $ os ++ "-" ++ show version ++ "-" ++ show date

-- There is also a monad transformer version of Cont.
-- The Functor, Applicative and Monad instances for ContT are identical to Cont.
newtype ContT m a = ContT {unContT ∷ ∀ r. (a → m r) → m r}

-----------------------
-- Existential Types --
-----------------------

-- An existential data type is one that is not defined in terms of a concrete type,
-- but in terms of a quantified type variable (a type variable with ∀), introduced on
-- the right-hand side of the data declaration.

-- Existential types have sort of an identity problem - the type system has forgotten what they are!

-- simpler example as introduction
-- `Any` is capable of storing a value of any type, and in doing so, forgets what type it has.
-- The type constructor doesn't have any type variables, and so it can't remember anything.
-- There's nowhere for it to store that information.
-- This `a` type exists only within the context of the Any data constructor; it is EXISTENTIAL!
data Any = ∀ a. Any a

-- # GADTAny
-- GADTs provide a more idiomatic syntax for this construction.
data Any' where
  Any' ∷ a → Any'

-- We can use Any to define a list with values of any types.
-- Its usefulness is limited due to the fact that its values can never be recovered.
-- >>> :type [Any 5, Any True, Any "hello"]
-- [Any 5, Any True, Any "hello"] ∷ [Any]

-- Existential types can be eliminated/consumed.
-- Note where the `a` and `r` types are quantified.
elimAny ∷ (∀ a. a → r) → Any → r
elimAny f (Any a) = f a

-- The caller of elimAny gets to decide the result `r`. But `a` is determined by the type inside of the Any.
-- Functions of type `∀ a. a → r` can only ever return constant values.
-- The polymorphism on their input doesn't allow any form of inspection.
-- >>> elimAny (const 5) (Any [1..5])
-- 5

-- >>> elimAny length (Any [1..5])
-- Couldn't match type `a_a1Oq9[sk:2]' with `[a0_a1Oqc[tau:2]]'

-- The definition of HasShow is remarkably similar to the GADT definition of Any, with the addition of the `Show t ⇒ constraint`.
-- This constraint requires a Show instance whenever constructing a HasShow, and Haskell will remember this.
-- Because a Show instance was required to build a HasShow, whatever type is inside of HasShow must have a Show instance.
-- Remarkably, Haskell is smart enough to realize this, and allow us to call show on whatever type exists inside.
data HasShow where
  HasShow ∷ Show a ⇒ a → HasShow

-- We can use this fact to write a Show instance for HasShow.
instance Show HasShow where
  show ∷ HasShow → String
  show (HasShow a) = show a

-- We are able to write an eliminator for HasShow which knows we have a Show dictionary in scope.
elimHasShow ∷ (∀ a. Show a ⇒ a → r) → HasShow → r
elimHasShow f (HasShow a) = f a

-- `Show HasShow` in terms of elimHasShow
-- instance Show HasShow where
--   show ∷ HasShow → String
--   show = elimHasShow show

-- >>> HasShow 5
-- 5

-------------------
-- Dynamic Types --
-------------------

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
pyPlus a b =
  fromMaybe (error "bad types for pyPlus") $
    asum
      [ liftD2 @String @String a b (++),
        liftD2 @Int @Int a b (+),
        liftD2 @String @Int a b $ \strA intB → strA ++ show intB,
        liftD2 @Int @String a b $ \intA strB → show intA ++ strB
      ]

-- >>> default (Int) -- set the default numeric type to Int (to construct Dynamics without type signatures)
-- >>> fromDynamic @Int (pyPlus ( Dynamic 1) ( Dynamic 2))
-- Just 3

-- >>> fromDynamic @String (pyPlus (Dynamic "hello") (Dynamic " world"))
-- Just "hello world"

-- >>> default (Int)
-- >>> fromDynamic @String (pyPlus (Dynamic 4) (Dynamic " minute"))
-- Just "4 minute"

-- >>> default (Int)
-- >>> fromDynamic @String (pyPlus (Dynamic "minute ") (Dynamic 4))
-- Just "minute 4"

-- show the actual type of a Dynamic
typeOf ∷ Dynamic → String
typeOf = elimDynamic $ \(_ ∷ t) → show . typeRep $ Proxy @t

-- >>> typeOf (Dynamic 5)
-- "Integer"

-- >>> typeOf (Dynamic "hello")
-- "[Char]"

-- Dynamically typed languages are merely strongly typed languages with a single type! ;-)

------------------------------------------------
-- Generalized Constraint Kinded Existentials --
------------------------------------------------

-- The definitions of HasShow and Dynamic are nearly identical.
-- data HasShow where
--   HasShow ∷ Show a ⇒ a → HasShow

-- data Dynamic where
--   Dynamic ∷ Typeable t ⇒ t → Dynamic

-- clear pattern to be factored out
-- By enabling ConstraintKinds, we are able to be polymorphic over Constraints.
data Has (c ∷ Type → Constraint) where
  Has ∷ c t ⇒ t → Has c

-- eliminate any constraint
elimHas ∷ (∀ a. c a ⇒ a → r) → Has c → r
elimHas f (Has a) = f a

-- We can thus implement HasShow and Dynamic as type synonyms.
-- type HasShow = Has Show
-- type Dynamic = Has Typeable

-- We want to use multiple constraints at once.
isMempty ∷ (Monoid a, Eq a) ⇒ a → Bool
isMempty a = a == mempty

-- Maybe we'd like to construct an Has around this constraint, (Monoid a, Eq a).
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
-- We're unable to talk about MonoidAndEq in its unsaturated form.
-- Only `MonoidAndEq a` is acceptable to the compiler.

-- There is a solution for Constraint synonyms (though not for Type synonyms in general.)
-- We can instead define a new class with a superclass constraint, and an instance that comes for
-- free given those same constraints.
-- This is known as a CONSTRAINT SYNONYM.
-- While type synonyms are unable to be partially applied, classes have no such restriction!
class (Monoid a, Eq a) ⇒ MonoidEq a

instance (Monoid a, Eq a) ⇒ MonoidEq a

-- >>> let hasMonoidEq = Has [] ∷ Has MonoidEq
-- >>> elimHas isMempty hasMonoidEq
-- True

-- >>> let hasMonoidEq = Has [True] ∷ Has MonoidEq
-- >>> elimHas isMempty hasMonoidEq
-- False

newtype Codensity a = Codensity {runCodensity ∷ ∀ r. (a → r) → r}

instance Functor Codensity where
  fmap f (Codensity c) = Codensity $ \c' → c (c' . f)

instance Applicative Codensity where
  pure a = Codensity $ \c → c a
  Codensity f <*> Codensity a = Codensity $ \br → f $ \ab → a $ br . ab

instance Monad Codensity where
  return = pure
  Codensity m >>= f = Codensity $ \c → m $ \a → runCodensity (f a) c

newtype CodensityT m a = CodensityT {unCodensityT ∷ ∀ r. (a → m r) → m r}

instance Functor (CodensityT m) where
  fmap f (CodensityT c) = CodensityT $ \c' → c (c' . f)

instance Applicative (CodensityT m) where
  pure a = CodensityT $ \c → c a
  CodensityT f <*> CodensityT a = CodensityT $ \br → f $ \ab → a $ br . ab

instance Monad (CodensityT m) where
  return = pure
  CodensityT m >>= f = CodensityT $ \c → m $ \a → unCodensityT (f a) c

instance MonadTrans CodensityT where
  lift m = CodensityT (m >>=)
