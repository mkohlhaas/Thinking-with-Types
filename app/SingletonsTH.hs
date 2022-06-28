-- # pragmas
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module SingletonsTH where

-- # imports
import Data.Ord.Singletons (EQSym0, GTSym0, LTSym0, POrd (Compare), SOrd (sCompare), SOrdering (SEQ, SGT, SLT), ThenCmpSym0, sThenCmp)
import Data.Singletons.TH (singletons)
import Prelude.Singletons (FalseSym0, FoldlSym0, NilSym0, PEq (type (==)), PShow (ShowsPrec), SBool (SFalse, STrue), SEq ((%==)), SFoldable (sFoldl), SList (SNil), SShow (sShowsPrec), ShowStringSym0, TrueSym0, sShowString)

-- # TimeOfDay
singletons
  [d|
    data TimeOfDay
      = Morning
      | Afternoon
      | Evening
      | Night
      deriving (Eq, Ord, Show)
    |]
