{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}

module OpenSum where

-- Extensible sum type

-- Motivation
-- Python's dictionary datatype:
-- record = { 'foo': 12, 'bar': True } -- type: `{foo ∷ Int, bar ∷ Bool}`.
-- record['qux'] = "hello"             -- gains a `qux ∷ String` field
-- record['foo'] = [1, 2, 3]           -- type of foo changes from Int to [Int]

-- We want to build this sort of "extensible" record type.

import Data.Functor.Identity
import Data.Proxy (Proxy (Proxy))
import Fcf (Eval, Exp, FindIndex, FromMaybe, Stuck, TyEq, type (=<<))
import GHC.TypeLits (ErrorMessage (ShowType, Text, (:$$:), (:<>:)), KnownNat, TypeError, natVal)
import GHC.Types (Nat, Type)
import Unsafe.Coerce (unsafeCoerce)

-- An open sum is a container of a data whose type isn't known statically.
-- Furthermore, there are no guarantees that we know which types it might be,
-- since the list of types itself might be polymorphic.

-- Existential types are ones whose type has been forgotten by the type system.
-- As a result, we can use them to allow us to store any type inside of our open sum container.
-- We will constrain this later on.

-- OpenSum is a container of `f t`, where `t` has kind K.
-- Because `t` isn't mentioned in the return type of our constructor, `t` is EXISTENTIAL.
-- Once `t` enters an OpenSum, it can never be recovered.
-- Knowledge of what `t` is is lost forever.

-- GADTs provide a nice interface for defining and working with existential types.
-- `f` is an INDEXED TYPE, which means it provides a TYPE when given a `K`.
type OpenSum ∷ (k → Type) → [k] → Type
data OpenSum f ts where
  UnsafeOpenSum ∷ Int → f t → OpenSum f ts

-- It's a common pattern in type level programming to label raw data constructors as Unsafe,
-- and write smart constructors that enforce the safety.

-- The presence of `f` allows us to add a common shape to all the members of `ts`.
-- E.g., `OpenSum ((→) String) '[Int, Bool]` is capable of storing `String → Int` and `String → Bool`.
-- Users who just want to store regular types with no additional structure should let `f ∼ Identity`.

-- >>> :kind! OpenSum ((→) String) '[Int, Bool]
-- OpenSum ((→) String) '[Int, Bool] ∷ Type
-- = OpenSum ((→) [Char]) '[Int, Bool]

-- >>> :kind! OpenSum ((→) String) '[Int, Int → Bool]
-- OpenSum ((→) String) '[Int, Int → Bool] ∷ Type
-- = OpenSum ((→) [Char]) '[Int, Int → Bool]

-- The Int in the constructor is an index into `ts`.
-- First-class type family to find `t` in `ts`:
type FindElem ∷ k → [k] → Exp Nat

type FindElem key ts = FromMaybe Stuck =<< FindIndex (TyEq key) ts

-- Remember: At the type-level (⇐<)/fish-operator acts like regular function composition (.), (=<<)/bind behaves like function application ($).

-- FromMaybe ∷ ∀ k. k → Maybe k → k → Type
-- =<< ∷ ∀ a b. (a → Exp b) → Exp a → b → Type
-- FindIndex ∷ ∀ a. (a → Exp Bool) → [a] → Maybe Nat → Type

-- >>> :kind! Eval(FindElem Int '[Int, String])
-- Eval(FindElem Int '[Int, String]) ∷ Natural
-- = 0

-- >>> :kind! Eval(FindElem (Int → Bool) '[String, Int → Bool])
-- Eval(FindElem (Int → Bool) '[String, Int → Bool]) ∷ Natural
-- = 1

-- >>> :kind! Eval(FindElem String '[Int, String])
-- Eval(FindElem String '[Int, String]) ∷ Natural
-- = 1

-- >>> :kind! Eval(FindElem [Char] '[Int, String])
-- Eval(FindElem [Char] '[Int, String]) ∷ Natural
-- = 1

-- >>> :kind! Eval(FindElem Int '[Bool, String])
-- Eval(FindElem Int '[Bool, String]) ∷ Natural
-- = Stuck

-- A Stuck type family is one which can't be reduced any further.
-- We can exploit this property and ask whether FindElement evaluated fully by asking whether it's a KnownNat.
type Member t ts = KnownNat (Eval (FindElem t ts))

-- KnownNat creates a Constraint.
-- KnownNat ∷ Nat → Constraint

-- >>> :kind! Member String '[Bool, String]
-- Member String '[Bool, String] ∷ Constraint
-- = KnownNat 1

-- >>> :kind! Member Int '[Bool, String]
-- Member Int '[Bool, String] ∷ Constraint
-- = KnownNat Stuck

findElem ∷ ∀ t ts. Member t ts ⇒ Int
findElem = fromIntegral . natVal $ Proxy @(Eval (FindElem t ts))

-- >>> :type natVal (Proxy @2)
-- natVal (Proxy @2) ∷ Integer

-- >>> natVal (Proxy @42)
-- 42

-- >>> natVal (Proxy @2)
-- 2

-- A KnownNat constraint allows for reification of the NAT at the term-level.
-- We can get an Int corresponding to the NAT we had.
-- >>> findElem @Bool @'[Bool, String]
-- 0

-- >>> findElem @String @'[Bool, String]
-- 1

-- >>> findElem @Int @'[Bool, String]
-- No instance for (KnownNat Stuck) arising from a use of `findElem'

-- smart, type-safe constructor for OpenSums
-- `inj` allows injecting a `f t` into any `OpenSum f ts` as long as `t` is an element somewhere in `ts`.
inj ∷ ∀ f t ts. Member t ts ⇒ f t → OpenSum f ts
inj = UnsafeOpenSum (findElem @t @ts)

injTrue ∷ OpenSum Identity '[Bool, String]
injTrue = inj (Identity True) ∷ OpenSum Identity '[Bool, String]

-- >>> prj injTrue ∷ Maybe (Identity Int)
-- No instance for (KnownNat Stuck) arising from a use of `prj'
-- In the expression: prj injTrue ∷ Maybe (Identity Int)
-- In an equation for `it_adJQ':
--     it_adJQ = prj injTrue ∷ Maybe (Identity Int)

-- >>> let foo = inj (Identity True) ∷ OpenSum Identity '[ Bool , String ]
-- Not in scope: type constructor or class `Identity'

-- >>> :type inj @((→) String) @Int @'[Bool, Int]
-- inj @((→) String) @Int @'[Bool, Int] ∷ (String → Int) → OpenSum ((→) String) '[Bool, Int]

-- >>> :type inj @((→) String) @Int @'[Bool, Int] length
-- inj @((→) String) @Int @'[Bool, Int] length ∷ OpenSum ((→) String) '[Bool, Int]

-- >>> :type inj @((→) String) @String @'[Bool, Int]
-- No instance for (KnownNat Stuck) arising from a use of `inj'
-- In the expression: inj @((→) String) @String @'[Bool, Int]

-- take sth. out of the open sum type (projection)
prj ∷ ∀ f t ts. Member t ts ⇒ OpenSum f ts → Maybe (f t)
prj (UnsafeOpenSum i f) =
  if i == findElem @t @ts -- runtime(!) check that the Int type tag inside of OpenSum is the same as the type we're trying to extract it as
    then Just $ unsafeCoerce f -- convincing the type checker to give back a (non-existential) `t`
    else Nothing -- type tags are not the same

-- TODO
-- >>> let injection = inj @((→) String) @Int @'[Bool, Int] length
-- >>> :type (prj injection)
-- (prj injection) ∷ KnownNat (Eval (FromMaybe Stuck (Eval (If (TyEqImpl t Bool) (Pure ('Just 0)) (Map ((+) 1) =<< FindIndex (TyEq t) '[Int]))))) ⇒ Maybe (String → t)

-- injection ∷ String → GHC.Types.Any
-- injection = prj inj' -- fromJust (prj inj') "hello"
--   where
--     -- inj' ∷ OpenSum ((→) String) '[Bool, Int]
--     inj' = inj @((→) String) @Int @'[Bool, Int] -- length

-- >>> let injection = inj @((→) String) @Int @'[Bool, Int] (\str → length str)
-- >>> (fromJust (prj injection)) "hello"
-- No instance for (KnownNat Stuck) arising from a use of `it_acXv'
-- In the first argument of `evalPrint', namely `it_acXv'
-- In a stmt of an interactive GHCi command: evalPrint it_acXv

-- induction over an OpenSum
decompose ∷ OpenSum f (t ': ts) → Either (f t) (OpenSum f ts)
decompose (UnsafeOpenSum 0 t) = Left $ unsafeCoerce t
decompose (UnsafeOpenSum n t) = Right $ UnsafeOpenSum (n - 1) t

-- TODO
-- >>> decompose ... ???

-- If it's too hard to do at the type-level, it's OK to cheat and prove things at the term-level.
-- In these cases, unsafeCoerce can be your best friend so long as you're careful to hide the unsafe constructors.

instance Eq (OpenSum f '[]) where
  (==) ∷ ∀ k (f' ∷ k → Type). OpenSum f' '[] → OpenSum f' '[] → Bool
  _ == _ = True

instance (Eq (f t), Eq (OpenSum f ts)) ⇒ Eq (OpenSum f (t ': ts)) where
  (==) ∷ ∀ a (f' ∷ a → Type) (t' ∷ a) (ts' ∷ [a]). (Eq (f' t'), Eq (OpenSum f' ts')) ⇒ OpenSum f' (t' : ts') → OpenSum f' (t' : ts') → Bool
  a == b = decompose a == decompose b

-- widen the possibilities of an open sum
-- `weaken` tacks a type `t` in front of the list of possibilities
-- TODO: should't the new type APPENDED to the list and given the proper index???
weaken ∷ OpenSum f ts → OpenSum f (t ': ts)
weaken (UnsafeOpenSum n t) = UnsafeOpenSum (n + 1) t -- I think this is the wrong index

-- TODO
-- >>> weaken ... ???

-- By using a rank-n type, `match` is given a function that can provide a `b` regardless of what's inside the open sum.
-- In this case, inspecting the type tag isn't necessary.
match ∷ ∀ f ts b. (∀ t. f t → b {- rank-n type -}) → OpenSum f ts → b
match fn (UnsafeOpenSum _ t) = fn t

-- TODO
-- >>> match ... ???

-- The semantics of TypeError is that if GHC is ever asked to solve one,
-- it emits the given type error instead, and refuse to compile.

-- Note that FriendlyFindElem is defined as a type family, rather than a type synonym as FCFs usually are.
-- This is to delay the expansion of the type error so GHC doesn't emit the error immediately.
-- We now attempt to find `t` in `ts`, and use FromMaybe to emit a type error in the case that we didn't find it.
type FriendlyFindElem ∷ (k → Type) → k → [k] → Exp Nat
type family FriendlyFindElem f t ts where
  FriendlyFindElem f t ts =
    FromMaybe
      ( TypeError
          ( 'Text "Attempted to call `friendlyPrj' to produce a `"
              ':<>: 'ShowType (f t)
              ':<>: 'Text "'."
              ':$$: 'Text "But the OpenSum can only contain one of:"
              ':$$: 'Text "  "
                ':<>: 'ShowType ts
          )
      )
      =<< FindIndex (TyEq t) ts

friendlyPrj ∷ ∀ f t ts. (KnownNat (Eval (FriendlyFindElem f t ts)), Member t ts) ⇒ OpenSum f ts → Maybe (f t)
friendlyPrj = prj

-- >>> friendlyPrj
-- Attempted to call `friendlyPrj' to produce a `f_anco[sk:1]
--                                                 t_ancp[sk:1]'.
-- But the OpenSum can only contain one of:
--   ts_ancq[sk:1]
-- When checking the inferred type
--   it_anaY ∷ ∀ {k} {f ∷ k → Type} {t ∷ k} {ts ∷ [k]}.
--              (KnownNat
--                 (Eval (FromMaybe (TypeError ...) (Eval (FindIndex (TyEq t) ts)))),
--               KnownNat
--                 (Eval (FromMaybe Stuck (Eval (FindIndex (TyEq t) ts))))) ⇒
--              OpenSum f ts → Maybe (f t)
