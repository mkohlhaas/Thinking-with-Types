{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module SingletonsTH where

import Data.Ord.Singletons
import Data.Singletons.TH (singletons)
import Prelude.Singletons

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
