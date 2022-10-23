{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}

module ST where

--------------------------------------
-- Scoping Information Existentials --
--------------------------------------

-- Existential types can be used to prevent information from leaking outside of a desired scope.
-- E.g., it means we can ensure that allocated resources can't escape a pre-specified region.
-- We can use the type system to prove that a HTTP session token is quarantined within its request context,
-- or that a file handle doesn't persist after it's been closed.
-- Because existential types are unable to exist outside of their quantifier, we can use it as a scoping mechanism.
-- By tagging sensitive data with an existential type, the type system will refuse any attempts to move this data outside of its scope.

-- Haskell's ST (strict state) monad is the most famous example of this approach,
-- lending its name to the approach: the ST trick.
-- If you're unfamiliar with it, ST allows us to write stateful code including mutable variables to perform computations,
-- so long as the statefulness never leaves the monad.
-- In other words, ST allows you to compute pure functions using impure means.

-- The amazing thing is that ST is not some magical compiler primitive - it's just library code.
-- And we can implement it ourselves, assuming we're comfortable using a little unsafePerformIO!

-- It's not the presence of mutable variables that makes code hard to reason about.
-- So long as all of its mutations are kept local, we know that a computation is pure.
-- Mutable variables on their own do not cause us to lose referential transparency.
-- Referential transparency is lost when code relies on external mutable variables.
-- Doing so creates an invisible data dependency between our code and the state of its external variables.

-- It's completely safe to have mutable variables so long as you can prove they never escape.
-- The ST trick exists to prevent such things from happening.

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

-- At its heart, ST is just the Identity monad with a phantom `s` parameter.
-- The phantom type variable `s` exists only as a place to put our existential type tag.
newtype ST s a = ST {unsafeRunST ∷ a}

-- Applicative and Monad instances can be provided for ST.
-- To ensure that our "unsafe" IO is performed while it's actually still safe, these instances must be explicitly strict.
-- This is not necessary in general to perform the ST trick.
-- It's only because we will be using unsafePerformIO.
instance Functor (ST s) where
  fmap f (ST a) = seq a . ST $ f a

instance Applicative (ST s) where
  pure = ST
  ST f <*> ST a = seq f . seq a . ST $ f a

instance Monad (ST s) where
  ST a >>= f = seq a $ f a

-- Mutable variables can be introduced inside of the ST monad.
-- For our implementation, we can simply implement these in terms of IORefs.
-- IORef is a mutable variable in the `IO` monad.
-- Note that STRef also has a phantom `s` parameter.
-- This is not accidental. `s` acts as a label irrevocably knotting a STRef with the ST context.
newtype STRef s a = STRef {unSTRef ∷ IORef a}

-- Function wrappers for STRef around IORef.

-- create new STRefs (newIORef)
-- Creating a STRef gives us one whose `s` parameter is the same as ST's `s`.
-- This is the irrevocable linking between the two types.
newSTRef ∷ a → ST s (STRef s a)
newSTRef = pure . STRef . unsafePerformIO . newIORef

-- read STRefs (readIORef)
readSTRef ∷ STRef s a → ST s a
readSTRef = pure . unsafePerformIO . readIORef . unSTRef

-- write STRefs (writeIORef)
writeSTRef ∷ STRef s a → a → ST s ()
writeSTRef ref = pure . unsafePerformIO . writeIORef (unSTRef ref)

-- modify STRefs (readSTRef and writeSTRef)
modifySTRef ∷ STRef s a → (a → a) → ST s ()
modifySTRef ref f = do
  a ← readSTRef ref
  writeSTRef ref $ f a

-- Escaping from the ST monad. This is merely unsafeRunST, but with a specialized type signature.
-- Tagging `a` with an existential type: ST a ⇒ ∀ s. ST s a
-- Introduction of the ST trick: The type `(∀ s. ST s a)` indicates that runST is capable of
-- running only those STs which do not depend on their `s` parameter.
-- The ∀ here acts as a quantifier over `s`. The type variable exists in scope only within `ST s a`.
-- Because it's existential, without a quantifier, we have no way of talking about the type.
-- It simply doesn’t exist outside of its ∀!
-- And this is the secret to why the ST trick works.
-- We exploit this fact that existentials can't leave their quantifier in order to scope our data.
-- The "quarantined zone" is defined with an existential quantifier, we tag our quarantined data
-- with the resulting existential type, and the type system does the rest.
runST ∷ (∀ s. ST s a) → a
runST = unsafeRunST

safeExample ∷ ST s String
safeExample = do
  ref ← newSTRef "hello"
  modifySTRef ref (++ " world")
  readSTRef ref

-- >>> runST safeExample
-- "hello world"

-- >>> :type runST safeExample
-- runST safeExample :: String

-- The type system disallows any code that would leak a reference to a STRef.
-- >>> runST (newSTRef True)
-- Couldn't match type ...

-- >>> :type newSTRef True
-- newSTRef True ∷ ST s (STRef s Bool)

-- signature of runST for `newSTRef True`
--    Type variable `s` is introduced and scoped.
--            |                    Later `s` is referenced.
--            |              But at this point the type no longer exists.
--            |                     There isn't any type `s` in scope!
--            |                               |
-- runST ∷ (∀ s. ST s (STRef s Bool)) → STRef s Bool

-- signature of runST for safeExample
--    Type variable `s` is introduced and scoped.
--            |                    There is no reference to `s`.
--            |                             |
-- runST ∷ (∀ s. ST s (STRef s String)) → String

-- GHC calls `s` a rigid skolem type variable.
-- Rigid variables are those that are constrained by a type signature written by a programmer.
-- In other words, they are not allowed to be type inferred.
-- A skolem is, for all intents and purposes, any existential type.
-- The purpose of the phantom s variable in ST and STRef is exactly to introduce a rigid skolem.
-- If it weren't rigid (specified), it would be free to vary, and Haskell would correctly infer that it is unused.
-- If it weren't a skolem, we would be unable to restrict its existence.

-- This ST trick can be used whenever you want to restrict the existence of some piece of data.
