{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module AdHocSingletons where

-- Dependent types depend on the result of runtime values.
-- Dependent types in Haskell can be approximated via singletons which can be understood as an isomorphism between terms and values.

-- The unit type `()` is a singleton, because it only has a single term, i.e. `()`.
-- Because of this one-to-one representation, we can think about the unit type as being able to cross the term-type divide at will.

-- Singleton types are just this idea taken to the extreme.
-- For every inhabitant of a type, we create a singleton type capable of bridging the term-type divide.
-- The singleton allows us to move between terms to types and vice versa.
-- As a result, we are capable of moving types to terms, using them in regular term-level Haskell
-- computations, and then lifting them back into types.

-- Notice that data kinds already give us type-level representations of terms.
-- Recall that `'True` is the promoted data constructor of `True`.

import Control.Monad.Trans.Writer (WriterT (runWriterT), tell)
import Data.Constraint (Dict (..))
import Data.Foldable (for_)
import Data.Kind (Type)

-- simple implementation of a singleton
-- The data constructors STrue and SFalse act as our bridge between the term and type-levels.
-- Both are terms, but are the sole inhabitants of their types.
-- We thus have isomorphisms `STrue ≌ 'True` and `SFalse ≌ 'False`.

-- finding an isomorphism between `Bool ≌ SBool b`.

-- going from `SBool b` to Bool is easy
fromSBool ∷ SBool b → Bool
fromSBool STrue = True
fromSBool SFalse = False

data SBool (b ∷ Bool) where
  STrue ∷ SBool 'True
  SFalse ∷ SBool 'False

-- The mapping from Bool to `SBool b` is not that easy,
-- because `SBool 'True` is a different type than `SBool 'False`.

-- introducing an existential wrapper SomeSBool
data SomeSBool where
  SomeSBool ∷ SBool b → SomeSBool

-- toSBool can now be written in terms of SomeSBool
toSBool ∷ Bool → SomeSBool
toSBool True = SomeSBool STrue
toSBool False = SomeSBool SFalse

-- so-called eliminator
withSomeSBool ∷ SomeSBool → (∀ (b ∷ Bool). SBool b → r) → r
withSomeSBool (SomeSBool s) f = f s

-- >>> withSomeSBool (toSBool True) fromSBool
-- True

-- >>> withSomeSBool (toSBool False) fromSBool
-- False

-- As an example of the usefulness of singletons, we will build a monad stack which can conditionally log messages.
-- These messages will only be for debugging, and thus should be disabled for production builds.
-- While one approach to this problem is to simply branch at runtime depending on whether logging is enabled,
-- this carries with it a performance impact.
-- Instead, we can conditionally choose our monad stack depending on a runtime value.

-- Monad Logging
-- typeclass indexed over Bool
class Monad (LoggingMonad b) ⇒ MonadLogging (b ∷ Bool) where
  type LoggingMonad b = (r ∷ Type → Type) | r → b -- associated type family to select the correct monad stack
  logMsg ∷ String → LoggingMonad b ()
  runLogging ∷ LoggingMonad b a → IO a

-- The `| r → b` notation is known as a type family dependency and acts as an injectivity annotation.
-- In other words, it tells Haskell that if it knows `LoggingMonad b` it can infer `b`.

-- unused
type family EnableLogging (b ∷ Bool) ∷ Type → Type where
  EnableLogging 'True = WriterT [String] IO
  EnableLogging 'False = IO

instance MonadLogging 'True where
  type LoggingMonad 'True = WriterT [String] IO
  logMsg ∷ String → WriterT [String] IO ()
  logMsg s = tell [s]
  runLogging ∷ WriterT [String] IO a → IO a
  runLogging m = do
    (a, w) ← runWriterT m
    for_ w putStrLn
    pure a

instance MonadLogging 'False where
  type LoggingMonad 'False = IO
  logMsg ∷ String → IO ()
  logMsg _ = pure ()
  runLogging ∷ IO a → IO a
  runLogging = id

program ∷ MonadLogging b ⇒ LoggingMonad b ()
program = do
  logMsg "hello world"
  pure ()

-- We help GHC by writing a function that can deliver dictionaries for any constraint that is total over Bool.
dict ∷
  ( c 'True {- dict works by requiring some `Bool → Constraint` to be satisfied for both 'True ...  -},
    c 'False {- ... and 'False -}
  ) ⇒
  SBool b {- takes a singleton and uses that to deliver the appropriate `Dict (c b)` by branching ... -} →
  Dict (c b)
dict STrue = Dict {- ... here. -}
dict SFalse = Dict

main ∷ Bool → IO ()
main bool = do
  withSomeSBool (toSBool bool) $ \(sb ∷ SBool b) →
    case dict @MonadLogging sb of
      Dict → runLogging @b program

-- >>> main True

{-

-- # badMain
main ∷ IO ()
main = do
  bool ← read <$> getLine         -- reads a Bool from stdin
  withSomeSBool (toSBool bool) $  -- lifts it into a singleton
    \(_ ∷ SBool b) →              -- the resulting existential type b is bound ...
      runLogging @b program       -- ... and type-applied in order to tell Haskell which monad stack it should use to run the program

-- Unfortunately, it fails to compile.

The problem is that typeclasses are implemented in GHC as implicitly passed variables.
At `runLogging @b program` GHC doesn't know the type of `b`, and thus can't find the appropriate MonadLogging dictionary,
even though MonadLogging is total and theoretically GHC should be able to determine this.

-}
