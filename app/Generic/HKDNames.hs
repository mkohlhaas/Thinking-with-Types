{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Generic.HKDNames where

import Data.Data (Proxy (..))
import Data.Functor.Const (Const (Const))
import Data.Kind (Constraint, Type)
import GHC.Generics (C1, D1, Generic, M1 (M1), Meta (MetaSel), S1, U1 (..), type (:*:) (..))
import GHC.TypeLits (KnownSymbol, symbolVal)
import Generics.Kind (Atom ((:@:)), Field (Field), GenericK (toK), LoT, LoT1, Var0)
import Generics.Kind.TH (deriveGenericK)

data Person f = Person {personAge ∷ f Int, personName ∷ f String}
  deriving (Generic)

deriving instance (Show (f Int), Show (f String)) ⇒ Show (Person f)

deriveGenericK ''Person

type HKDKind = (Type → Type) → Type

type GNames ∷ (LoT HKDKind → Type) → Constraint
class GNames f where
  gnames ∷ f (LoT1 (Const String))

instance (GNames f, GNames g) ⇒ GNames (f :*: g) where
  gnames = gnames :*: gnames

instance GNames f ⇒ GNames (C1 _1 f) where
  gnames = M1 gnames

instance GNames f ⇒ GNames (D1 _1 f) where
  gnames = M1 gnames

instance KnownSymbol name ⇒ GNames (S1 ('MetaSel ('Just name) _1 _2 _3) (Field (Var0 ':@: a))) where
  gnames = M1 $ Field $ Const $ symbolVal $ Proxy @name

instance GNames U1 where
  gnames = U1

personNames ∷ Person (Const String)
personNames = toK gnames
