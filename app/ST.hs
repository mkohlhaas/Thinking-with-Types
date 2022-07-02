{-# LANGUAGE UnicodeSyntax #-}

module ST where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

newtype ST s a = ST {unsafeRunST :: a}

instance Functor (ST s) where
  fmap f (ST a) = seq a . ST $ f a

instance Applicative (ST s) where
  pure = ST
  ST f <*> ST a = seq f . seq a . ST $ f a

instance Monad (ST s) where
  ST a >>= f = seq a $ f a

newtype STRef s a = STRef {unSTRef :: IORef a}

newSTRef ∷ a → ST s (STRef s a)
newSTRef = pure . STRef . unsafePerformIO . newIORef

readSTRef ∷ STRef s a → ST s a
readSTRef = pure . unsafePerformIO . readIORef . unSTRef

writeSTRef ∷ STRef s a → a → ST s ()
writeSTRef ref = pure . unsafePerformIO . writeIORef (unSTRef ref)

modifySTRef ∷ STRef s a → (a → a) → ST s ()
modifySTRef ref f = do
  a <- readSTRef ref
  writeSTRef ref $ f a

runST ∷ (∀ s. ST s a) → a
runST x = unsafeRunST x

{-

-- # runSTType
runST :: (∀ s. ST s a) -> a

-}

safeExample ∷ ST s String
safeExample = do
  ref <- newSTRef "hello"
  modifySTRef ref (++ " world")
  readSTRef ref

{-

-- # signature
runST
    :: (∀ s. ST s (STRef s Bool)) -- ! 1
    -> STRef s Bool  -- ! 2

-}
