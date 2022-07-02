{-# LANGUAGE UndecidableInstances, UnicodeSyntax #-}

module RankN where

import Control.Monad.Trans.Class (MonadTrans (..))
import Data.Foldable             (asum)
import Data.Kind                 (Constraint, Type)
import Data.Maybe                (fromMaybe)
import Data.Proxy                (Proxy (Proxy))
import Data.Typeable             (Typeable, cast, typeRep)

applyToFive ∷ (∀ a. a → a) → Int
applyToFive f = f 5

{-

-- # ∀1
∀ a. a -> a

-- # ∀2
∀ a. (a -> a)

-- # ∀3
∀ r. ((∀ a. (a -> r)) -> r)

id :: ∀ a. a -> a
id a = a

-- # brokenApply
applyToFive :: (a -> a) -> Int
applyToFive f = f 5

-- # explicitBrokenApply
applyToFive :: ∀ a. (a -> a) -> Int
applyToFive f = f 5

-}

toCont ∷ a → (∀ r. (a → r) → r)
toCont a callback = callback a

isMempty ∷ (Monoid a, Eq a) ⇒ a → Bool
isMempty a = a == mempty

fromCont ∷ (∀ r. (a → r) → r) → a
fromCont f =
  let callback = id
   in f callback

newtype Codensity a = Codensity {runCodensity :: ∀ r. (a → r) → r}

newtype Cont r a = Cont {unCont :: (a → r) → r}

-- # contFunctor
instance Functor Codensity where
  fmap f (Codensity c) = Codensity $ \c' -> c (c' . f)

-- # contApplicative
instance Applicative Codensity where
  pure a = Codensity $ \c -> c a
  Codensity f <*> Codensity a = Codensity $ \br -> f $ \ab -> a $ br . ab

-- # contMonad
instance Monad Codensity where
  return = pure
  Codensity m >>= f = Codensity $ \c -> m $ \a -> runCodensity (f a) c

newtype CodensityT m a = CodensityT {unCodensityT :: ∀ r. (a → m r) → m r}

instance Functor (CodensityT m) where
  fmap f (CodensityT c) = CodensityT $ \c' -> c (c' . f)

instance Applicative (CodensityT m) where
  pure a = CodensityT $ \c -> c a
  CodensityT f <*> CodensityT a = CodensityT $ \br -> f $ \ab -> a $ br . ab

instance Monad (CodensityT m) where
  return = pure
  CodensityT m >>= f = CodensityT $ \c -> m $ \a -> unCodensityT (f a) c

instance MonadTrans CodensityT where
  lift m = CodensityT (m >>=)

releaseString ∷ String
releaseString =
  withVersionNumber $ \version ->
    withTimestamp $ \date ->
      withOS $ \os ->
        os ++ "-" ++ show version ++ "-" ++ show date

withVersionNumber ∷ (Double → r) → r
withVersionNumber f = f 1.0

withTimestamp ∷ (Int → r) → r
withTimestamp f = f 1532083362

withOS ∷ (String → r) → r
withOS f = f "linux"

releaseStringCodensity ∷ String
releaseStringCodensity = fromCont $
  runCodensity $ do
    version <- Codensity withVersionNumber
    date <- Codensity withTimestamp
    os <- Codensity withOS
    pure $ os ++ "-" ++ show version ++ "-" ++ show date

data Any = ∀ a. Any a

elimAny ∷ (∀ a. a → r) → Any → r
elimAny f (Any a) = f a

data Has (c :: Type → Constraint) where
  Has :: c t => t -> Has c

elimHas ∷ (∀ a. c a ⇒ a → r) → Has c → r
elimHas f (Has a) = f a

data HasShow where
  HasShow :: Show t => t -> HasShow

elimHasShow ∷ (∀ a. Show a ⇒ a → r) → HasShow → r
elimHasShow f (HasShow a) = f a

-- # hasShowShow
instance Show HasShow where
  show (HasShow s) = "HasShow " ++ show s

{-

-- # showElimHasShow
instance Show HasShow where
  show = elimHasShow show

-}

data Dynamic where
  Dynamic :: Typeable t => t -> Dynamic

elimDynamic ∷ (∀ a. Typeable a ⇒ a → r) → Dynamic → r
elimDynamic f (Dynamic a) = f a

fromDynamic ∷ Typeable a ⇒ Dynamic → Maybe a
fromDynamic = elimDynamic cast

liftD2 ∷ ∀ a b r. (Typeable a, Typeable b, Typeable r) ⇒ Dynamic → Dynamic → (a → b → r) → Maybe Dynamic
liftD2 d1 d2 f = fmap Dynamic . f <$> fromDynamic @a d1 <*> fromDynamic @b d2

pyPlus ∷ Dynamic → Dynamic → Dynamic
pyPlus a b =
  fromMaybe (error "bad types for pyPlus") $
    asum
      [ liftD2 @String @String a b (++),
        liftD2 @Int @Int a b (+),
        liftD2 @String @Int a b $ \strA intB ->
          strA ++ show intB,
        liftD2 @Int @String a b $ \intA strB ->
          show intA ++ strB
      ]

typeOf ∷ Dynamic → String
typeOf = elimDynamic $ \(_ :: t) -> show . typeRep $ Proxy @t

type MonoidAndEq a = (Monoid a, Eq a)

-- # MonoidEq
class (Monoid a, Eq a) => MonoidEq a

instance (Monoid a, Eq a) ⇒ MonoidEq a

{-

-- # GADTAny
data Any where
  Any :: a -> Any

-- # typeHasShow
type HasShow = Has Show
type Dynamic = Has Typeable

-}
