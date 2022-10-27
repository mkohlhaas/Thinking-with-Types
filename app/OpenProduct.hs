{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE InstanceSigs #-}

module OpenProduct where

-- The implementation will associate names with each type inside.
-- These names can later be used by the user to refer back to the data contained.
-- As a result, the majority of our implementation will be type-level book-keeping.

import Data.Constraint (Constraint)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Vector qualified as V
import Fcf (Eval, Exp, Filter, FindIndex, FromMaybe, Fst, Lookup, Map, Not, Null, SetIndex, Stuck, TyEq, type (<=<), type (=<<))
import GHC.OverloadedLabels -- (IsLabel (..))
import GHC.TypeLits (ErrorMessage (..), KnownNat, Nat, Symbol, TypeError, natVal)
import Unsafe.Coerce (unsafeCoerce)

-- defining a container Any that will existentialize away its `k` index
data Any (f ∷ k → Type) where
  Any ∷ f t → Any f

-- defining OpenProduct as a Data.Vector of Anys
-- TODO(sandy): this annotation is probably wrong
type OpenProduct ∷ (k → Type) → [(Symbol, k)] → Type
data OpenProduct f ts where
  OpenProduct ∷ V.Vector (Any f) → OpenProduct f ts

-- an empty OpenProduct has an empty list of types and an empty Vector
nil ∷ OpenProduct f '[]
nil = OpenProduct V.empty

-- Because all data inside an OpenProduct will be labeled by a SYMBOL,
-- we need a way for users to talk about SYMBOLs at the term-level
data Key (key ∷ Symbol) = Key

-- >>> :type Key @"myData"
-- Key @"myData" :: Key "myData"

-- adds a new '(key, k) to the head of the type list,
-- and inserts the `f k` to the head of the internal Vector.
-- In this way, it preserves the invariant that our list of types has the same ordering as the data in.
badInsert ∷ Key key → f t → OpenProduct f ts → OpenProduct f ('(key, t) ': ts)
badInsert _ ft (OpenProduct v) = OpenProduct $ V.cons (Any ft) v

-- >>> let result = badInsert (Key @"key") (Just "hello") nil
-- >>> :type result
-- result :: OpenProduct Maybe '[ '("key", String)]

-- >>> let result1 = badInsert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = badInsert (Key @"key2") (Just True) result1
-- >>> :type result2
-- result2 :: OpenProduct Maybe '[ '("key2", Bool), '("key1", String)]

-- Same key, different values - not ideal
-- >>> let result1 = badInsert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = badInsert (Key @"key1") (Just True) result1
-- >>> :type result2
-- result2 :: OpenProduct Maybe '[ '("key1", Bool), '("key1", String)]

-- type family UniqueKey computes whether a key is unique
-- UniqueKey is the type-level equivalent of `null . filter (== key) . fst`.
type UniqueKey ∷ k → [(k, t)] → Exp Bool
type UniqueKey key ts = Null =<< Filter (TyEq key <=< Fst) ts

-- TODO
-- >>> :kind! Eval(UniqueKey (Key @"key3") '[ '( "key1", Bool), '( "key2", String)])

oldInsert ∷ Eval (UniqueKey key ts) ~ 'True ⇒ Key key → f t → OpenProduct f ts → OpenProduct f ('(key, t) ': ts)
oldInsert _ ft (OpenProduct v) = OpenProduct $ V.cons (Any ft) v

-- >>> let result = oldInsert (Key @"key") (Just "hello") nil
-- >>> :type result
-- result :: OpenProduct Maybe '[ '("key", String)]

-- >>> let result1 = oldInsert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = oldInsert (Key @"key2") (Just True) result1
-- >>> :type result2
-- result2 :: OpenProduct Maybe '[ '("key2", Bool), '("key1", String)]

-- no double insert possible
-- >>> let result1 = oldInsert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = oldInsert (Key @"key1") (Just True) result1
-- >>> :type result2
-- Couldn't match type 'False with 'True

-- lookup in list of types to figure out which index of the Vector to return.
type FindElem ∷ Symbol → [(Symbol, k)] → Nat
type FindElem key ts = Eval (FromMaybe Stuck =<< FindIndex (TyEq key <=< Fst) ts)

-- >>> :kind! (FindElem "key1" '[ '("key1", Bool)])
-- (FindElem "key1" '[ '( "key1", Bool)]) :: Natural
-- = 0

-- >>> :kind! (FindElem "key3" '[ '("key1", Bool), '("key2", Int), '("key3", String)])
-- (FindElem "key3" '[ '("key1", Bool), '("key2", Int), '("key3", String)]) :: Natural
-- = 2

-- >>> :kind! (FindElem "key2" '[ '("key1", Bool)])
-- (FindElem "key2" '[ '( "key1", Bool)]) :: Natural
-- = Stuck

findElem ∷ ∀ key ts. KnownNat (FindElem key ts) ⇒ Int
findElem = fromIntegral . natVal $ Proxy @(FindElem key ts)

-- >>> findElem @"key1" @'[ '("key1", Bool)]
-- 0

-- >>> findElem @"key3" @'[ '("key1", Bool), '("key2", Int), '("key3", String)]
-- 2

type LookupType ∷ k → [(k, t)] → Exp t
type LookupType key ts = FromMaybe Stuck =<< Lookup key ts

get ∷ ∀ key ts f. KnownNat (FindElem key ts) ⇒ Key key → OpenProduct f ts → f (Eval (LookupType key ts))
get _ (OpenProduct v) = unAny $ V.unsafeIndex v $ findElem @key @ts
  where
    unAny (Any a) = unsafeCoerce a

-- >>> get (Key @"key1") (oldInsert (Key @"key1") (Just "hello2") nil)
-- Just "hello2"

-- >>> let result1 = oldInsert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = oldInsert (Key @"key2") (Just True) result1
-- >>> get (Key @"key2") result2
-- Just True

-- scans through `ts` and sets the type associated with `key` to `t`
type UpdateElem ∷ Symbol → k → [(Symbol, k)] → Exp [(Symbol, k)]
type UpdateElem key t ts = SetIndex (FindElem key ts) '(key, t) ts

-- TODO
-- >>> kind! Eval(UpdateElem (Key @"key1") '[ '("key1", Bool), '("key2", Int), '("key3", String)])
-- parse error on input '

-- update the value stored in our Vector at the same place we want to replace the type in `ts`
update ∷ ∀ key ts t f. KnownNat (FindElem key ts) ⇒ Key key → f t → OpenProduct f ts → OpenProduct f (Eval (UpdateElem key t ts))
update _ ft (OpenProduct v) = OpenProduct $ v V.// [(findElem @key @ts, Any ft)]

-- TODO
-- >>> let result1 = oldInsert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = oldInsert (Key @"key2") (Just True) result1
-- >>> update (Key @"key1") Maybe result2
-- Illegal term-level use of the type constructor `Maybe'
--   imported qualified from `Prelude'
--   (and originally defined in `GHC.Maybe')
-- In the second argument of `update', namely `Maybe'
-- In the expression: update (Key @"key1") Maybe result2
-- In an equation for `it_a6Nix':
--     it_a6Nix = update (Key @"key1") Maybe result2

-- OverloadedLabels:  "get #example foo" ⇒ "get (Key @"example") foo"
-- Notice that the instance head is not of the form
-- `IsLabel key (Key key)`, but instead has two type variables
-- `key` and `key'`) which are then asserted to be the same.
-- This odd phrasing is due to a quirk with Haskell's instance resolution,
-- and is known as the CONSTRAINT TRICK.
instance (key ~ key') ⇒ IsLabel key (Key key') where
  fromLabel ∷ (key ~ key') ⇒ Key key'
  fromLabel = Key

-- >>> get (Key @"key1") (oldInsert (Key @"key1") (Just "hello2") nil)
-- Just "hello2"

-- >>> get #key1 (oldInsert #key1 (Just "hello1") nil)
-- Just "hello1"

overloadedKey ∷ Maybe [Char]
overloadedKey = get #key1 (oldInsert #key1 (Just "hello1") nil)

-- >>> overloadedKey
-- Just "hello1"

type RequireUniqueKey ∷ Bool → Symbol → k → [(Symbol, k)] → Constraint
type family RequireUniqueKey result key t ts where
  RequireUniqueKey 'True key t ts = () -- UNIT CONSTRAINT (); needs ConstraintKinds or the like
  RequireUniqueKey 'False key t ts =
    TypeError
      ( 'Text "Attempting to add a field named `"
          ':<>: 'Text key
          ':<>: 'Text "' with type "
          ':<>: 'ShowType t
          ':<>: 'Text " to an OpenProduct."
          ':$$: 'Text "But the OpenProduct already has a field `"
            ':<>: 'Text key
            ':<>: 'Text "' with type "
            ':<>: 'ShowType (LookupType key ts)
          ':$$: 'Text "Consider using `update' "
            ':<>: 'Text "instead of `insert'."
      )

insert ∷ RequireUniqueKey (Eval (UniqueKey key ts)) key t ts ⇒ Key key → f t → OpenProduct f ts → OpenProduct f ('(key, t) ': ts)
insert _ ft (OpenProduct v) = OpenProduct $ V.cons (Any ft) v

-- >>> let result1 = insert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = insert (Key @"key2") (Just True) result1
-- >>> :type result2
-- result2 :: OpenProduct Maybe '[ '("key2", Bool), '("key1", String)]

-- >>> let result1 = insert (Key @"key1") (Just "hello2") nil
-- >>> let result2 = insert (Key @"key1") (Just True) result1
-- >>> :type result2
-- Attempting to add a field named `key1' with type Bool to an OpenProduct.
-- But the OpenProduct already has a field `key1' with type FromMaybe
--                                                            Stuck
--                                                          =<< Lookup "key1" '[ '("key1", String)]
-- Consider using `update' instead of `insert'.
-- In the expression: insert (Key @"key1") (Just True) result1
-- In an equation for `result2_a17HT':
--     result2_a17HT = insert (Key @"key1") (Just True) result1


-- upsert
--     ∷ Key key
--     → f t
--     → OpenProduct f ts
--     → OpenProduct f (Eval (UpsertElem key t ts))
-- upsert = undefined

data Placeholder1Of3 ∷ (a → b → c → Exp r) → b → c → a → Exp r

-- # EvalPlaceholder
type instance Eval (Placeholder1Of3 f b c a) = Eval (f a b c)

type UpsertLoc ∷ Symbol → [(Symbol, k)] → Maybe Nat
type UpsertLoc key ts = Eval (FindIndex (TyEq key <=< Fst) ts)

class FindUpsertElem (a ∷ Maybe Nat) where
  upsertElem ∷ Maybe Int

-- # FindUpsertNothing
instance FindUpsertElem 'Nothing where
  upsertElem = Nothing

-- # FindUpsertJust
instance KnownNat n ⇒ FindUpsertElem ('Just n) where
  upsertElem = Just . fromIntegral . natVal $ Proxy @n

type UpsertElem ∷ Symbol → k → [(Symbol, k)] → Exp [(Symbol, k)]
type UpsertElem key t ts =
  FromMaybe ('(key, t) ': ts)
    =<< Map (Placeholder1Of3 SetIndex '(key, t) ts) -- ! 1
    =<< FindIndex (TyEq key <=< Fst) ts

upsert ∷ ∀ key ts t f. FindUpsertElem (UpsertLoc key ts) ⇒ Key key → f t → OpenProduct f ts → OpenProduct f (Eval (UpsertElem key t ts))
upsert _ ft (OpenProduct v) =
  OpenProduct $ case upsertElem @(UpsertLoc key ts) of
    Nothing → V.cons (Any ft) v
    Just n → v V.// [(n, Any ft)]

type FriendlyFindElem ∷ Symbol → Symbol → [(Symbol, k)] → k
type family FriendlyFindElem funcName key ts where
  FriendlyFindElem funcName key ts =
    Eval
      ( FromMaybe
          ( TypeError
              ( 'Text "Attempted to call `"
                  ':<>: 'Text funcName
                  ':<>: 'Text "' with key `"
                  ':<>: 'Text key
                  ':<>: 'Text "'."
                  ':$$: 'Text "But the OpenProduct only has keys :"
                  ':$$: 'Text "  "
                    ':<>: 'ShowType (Eval (Map Fst ts))
              )
          )
          =<< FindIndex (TyEq key <=< Fst) ts
      )

type ShowList ∷ [k] → ErrorMessage
type family ShowList ts where
  ShowList '[] = 'Text ""
  ShowList (a ': '[]) = 'ShowType a
  ShowList (a ': as) = 'ShowType a ':<>: 'Text ", " ':<>: ShowList as

type FriendlyFindElem2 ∷ Symbol → Symbol → [(Symbol, k)] → k
type family FriendlyFindElem2 funcName key ts where
  FriendlyFindElem2 funcName key ts =
    Eval
      ( FromMaybe
          ( TypeError
              ( 'Text "Attempted to call `"
                  ':<>: 'Text funcName
                  ':<>: 'Text "' with key `"
                  ':<>: 'Text key
                  ':<>: 'Text "'."
                  ':$$: 'Text "But the OpenProduct only has keys :"
                  ':$$: 'Text "  "
                    ':<>: ShowList (Eval (Map Fst ts))
              )
          )
          =<< FindIndex (TyEq key <=< Fst) ts
      )

friendlyUpdate ∷ ∀ key ts t f. (KnownNat (FriendlyFindElem "friendlyUpdate" key ts), KnownNat (FindElem key ts)) ⇒ Key key → f t → OpenProduct f ts → OpenProduct f (Eval (UpdateElem key t ts))
friendlyUpdate _ ft (OpenProduct v) =
  OpenProduct $ v V.// [(findElem @key @ts, Any ft)]

type DeleteElem key = Filter (Not <=< TyEq key <=< Fst)

delete ∷ ∀ key ts f. KnownNat (FindElem key ts) ⇒ Key key → OpenProduct f ts → OpenProduct f (Eval (DeleteElem key ts))
delete _ (OpenProduct v) =
  let (a, b) = V.splitAt (findElem @key @ts) v
   in OpenProduct $ a V.++ V.tail b

friendlyDelete ∷ ∀ key ts f. (KnownNat (FriendlyFindElem "friendlyDelete" key ts), KnownNat (FindElem key ts)) ⇒ Key key → OpenProduct f ts → OpenProduct f (Eval (DeleteElem key ts))
friendlyDelete _ (OpenProduct v) =
  let (a, b) = V.splitAt (findElem @key @ts) v
   in OpenProduct $ a V.++ V.tail b

peel ∷ ∀ f name t ts. OpenProduct f ('(name, t) ': ts) → (f t, OpenProduct f ts)
peel z@(OpenProduct v) = (get (Key @name) z, OpenProduct $ V.tail v)

instance Eq (OpenProduct f '[]) where
  _ == _ = True

instance (Eq (f t), Eq (OpenProduct f ts)) ⇒ Eq (OpenProduct f ('(name, t) ': ts)) where
  a == b = peel a == peel b
