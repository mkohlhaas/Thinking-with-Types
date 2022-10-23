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
-- Introduction of the ST trick: The type `(forall s. ST s a)` indicates that runST is capable of
-- running only those STs which do not depend on their `s` parameter.
runST ∷ (∀ s. ST s a) → a
runST = unsafeRunST

safeExample ∷ ST s String
safeExample = do
  ref ← newSTRef "hello"
  modifySTRef ref (++ " world")
  readSTRef ref

-- >>> runST safeExample
-- "hello world"

-- The type system disallows any code that would leak a reference to a STRef.
-- >>> runST (newSTRef True)
-- Couldn't match type ...

{-

-- # runSTType
runST ∷ (∀ s. ST s a) → a

-}

{-

-- # signature
runST
    ∷ (∀ s. ST s (STRef s Bool)) -- ! 1
    → STRef s Bool  -- ! 2

-}
