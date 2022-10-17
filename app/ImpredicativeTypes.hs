{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module ImpredicativeTypes where

import Control.Concurrent (MVar, forkIO, newEmptyMVar, putMVar, takeMVar, threadDelay)
import Control.Exception (bracket_)
import Control.Monad (void)

makeSerial ∷ IO (∀ a. IO a → IO a)
makeSerial = fmap locking newEmptyMVar

locking ∷ MVar () → (∀ a. IO a → IO a)
locking lock = bracket_ (putMVar lock ()) (takeMVar lock)

dump ∷ (IO () → IO ()) → IO ()
dump f = void $
  forkIO $ do
    f $ putStrLn "hello"
    f $ putStrLn "hello"

serialized ∷ IO ()
serialized = do
  makeSerial >>= \serial → do
    -- ! 1
    dump serial
    dump serial

  threadDelay 100000

interleaved ∷ IO ()
interleaved = do
  dump id
  dump id

  threadDelay 100000

yo ∷ (∀ a. [a] → [a]) → Int
yo _ = 0

($$) ∷ (a → b) → a → b
g $$ a = g a

blah ∷ Int
blah = yo $$ reverse
