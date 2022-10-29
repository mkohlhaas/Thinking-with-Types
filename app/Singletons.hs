{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE InstanceSigs #-}

module Singletons where

import Data.Typeable (type (:~:) (..))
import Data.Void (Void)
import Unsafe.Coerce (unsafeCoerce)

data family Sing (a ∷ k)

data SomeSing k where
  SomeSing ∷ Sing (a ∷ k) → SomeSing k

-- eliminator
withSomeSing ∷ SomeSing k → (∀ (a ∷ k). Sing a → r) → r
withSomeSing (SomeSing s) f = f s

-- packaging together toSing and fromSing into a typeclass
class SingKind k where
  type Demote k = r | r → k
  toSing ∷ Demote k → SomeSing k
  fromSing ∷ Sing (a ∷ k) → Demote k -- type variable k is used both as a type and a kind

------------------------
-- Instances for Bool --
------------------------

-- Sing Bool
data instance Sing (a ∷ Bool) where
  STrue ∷ Sing 'True
  SFalse ∷ Sing 'False

-- Sing KindBool
instance SingKind Bool where
  type Demote Bool = Bool
  toSing ∷ Demote Bool → SomeSing Bool
  toSing True = SomeSing STrue
  toSing False = SomeSing SFalse
  -- fromSing ∷ Sing a → Demote Bool
  fromSing STrue = True
  fromSing SFalse = False

-- >>> withSomeSing (toSing True) fromSing
-- True

-- >>> withSomeSing (toSing False) fromSing
-- False

-- Because singletons are the unique inhabitant of their types, at the term-level they are isomorphic with ().
-- Therefore, we expect to be able to get this unique inhabitant, in the same way we can always conjure a () out of thin air.

class SingI (a ∷ k) where
  sing ∷ Sing a

---------------------------------
-- Instances of SingI for Bool --
---------------------------------

-- SingI True
instance SingI 'True where
  sing ∷ Sing 'True
  sing = STrue

-- SingI False
instance SingI 'False where
  sing ∷ Sing 'False
  sing = SFalse

-- TODO (book seems to be wrong here)
-- >>> :type sing @'True
-- Expected a type, but 'True has kind `Bool'
-- In the type 'True
-- In the expression: sing @'True

-- Sing Maybe
data instance Sing (a ∷ Maybe k) where
  SJust ∷ Sing (a ∷ k) → Sing ('Just a)
  SNothing ∷ Sing 'Nothing

-- SingI Nothing
instance SingI 'Nothing where
  sing ∷ Sing 'Nothing
  sing = SNothing

-- SingI Just
instance SingI a ⇒ SingI ('Just a) where
  sing ∷ ∀ a1 (a2 ∷ a1). SingI a2 ⇒ Sing ('Just a2)
  sing = SJust sing

-- Sing KindMaybe
instance (k ~ Demote k, SingKind k) ⇒ SingKind (Maybe k) where
  type Demote (Maybe k) = Maybe k
  toSing ∷ (k ~ Demote k, SingKind k) ⇒ Demote (Maybe k) → SomeSing (Maybe k)
  toSing (Just a) = withSomeSing (toSing a) $ SomeSing . SJust
  toSing Nothing = SomeSing SNothing
  fromSing ∷ ∀ k' (a ∷ Maybe k'). (k' ~ Demote k', SingKind k') ⇒ Sing a → Demote (Maybe k')
  fromSing (SJust a) = Just $ fromSing a
  fromSing SNothing = Nothing

-- Sing List
data instance Sing (a ∷ [k]) where
  SNil ∷ Sing '[]
  SCons ∷ Sing (h ∷ k) → Sing (t ∷ [k]) → Sing (h ': t)

-- SingKind List
instance (k ~ Demote k, SingKind k) ⇒ SingKind [k] where
  type Demote [k] = [k]
  toSing ∷ (k ~ Demote k, SingKind k) ⇒ Demote [k] → SomeSing [k]
  toSing [] = SomeSing SNil
  toSing (h : t) =
    withSomeSing (toSing h) $ \sh →
      withSomeSing (toSing t) $ \st →
        SomeSing $ SCons sh st
  fromSing ∷ ∀ k' (a ∷ [k']). (k' ~ Demote k', SingKind k') ⇒ Sing a → Demote [k']
  fromSing SNil = []
  fromSing (SCons sh st) = fromSing sh : fromSing st

-- SingI Nil
instance SingI '[] where
  sing ∷ Sing '[]
  sing = SNil

-- SingI Cons
instance (SingI h, SingI t) ⇒ SingI (h ': t) where
  sing ∷ ∀ a (h' ∷ a) (t' ∷ [a]). (SingI h', SingI t') ⇒ Sing (h' : t')
  sing = SCons sing sing

data Decision a = Proved a | Disproved (a → Void) -- ! 1

class SDecide k where
  (%~) ∷ Sing (a ∷ k) → Sing (b ∷ k) → Decision (a :~: b)

-- Free SDecide
instance (Eq (Demote k), SingKind k) ⇒ SDecide k where
  (%~) ∷ ∀ k' (a ∷ k') (b ∷ k'). (Eq (Demote k'), SingKind k') ⇒ Sing a → Sing b → Decision (a :~: b)
  a %~ b =
    if fromSing a == fromSing b
      then Proved $ unsafeCoerce Refl
      else Disproved $ const undefined

-- SDecide Bool
instance SDecide Bool where
  -- (%~) ∷ Sing a → Sing b → Decision (a :~: b)
  STrue %~ STrue = Proved Refl
  SFalse %~ SFalse = Proved Refl
  _ %~ _ = Disproved $ const undefined

-- SDecide Maybe
instance SDecide a ⇒ SDecide (Maybe a) where
  (%~) ∷ ∀ a' (a1 ∷ Maybe a') (b ∷ Maybe a'). SDecide a' ⇒ Sing a1 → Sing b → Decision (a1 :~: b)
  SJust a %~ SJust b =
    case a %~ b of
      Proved Refl → Proved Refl
      Disproved _ → Disproved $ const undefined
  SNothing %~ SNothing = Proved Refl
  _ %~ _ = Disproved $ const undefined
