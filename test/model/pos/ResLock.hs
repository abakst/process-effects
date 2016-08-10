{- LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module ResLock where

import Control.Process.MessagePassing

data ResState   = Locked | Unlocked
data LockMsg    = Lock Pid
data Command    = Acquired
                | Unlock
                | ReqInc | ReqGet

instance RecvMsg LockMsg where
instance RecvMsg Command where
{-@ invariant {v:LockMsg | validMsg v} @-}
{-@ invariant {v:Command | validMsg v} @-}

main :: Process ()
main = do me <- getSelfPid
          spawnN n me
          resServer
  where
    n = 3 :: Int

resServer :: Process ()
resServer = resLoop Unlocked
  where
    resLoop Unlocked
      = do lock <- recv
           case lock of
             Lock p ->
               do send p Acquired
                  resLoop Locked
    resLoop Locked
      = do request <- recv
           case request of
             ReqInc -> resLoop Locked
             ReqGet -> resLoop Locked
             Unlock  -> resLoop Unlocked

client :: Pid -> Process ()
client r = do me <- getSelfPid
              send r (Lock me)
              msg <- recv
              case msg of
                Acquired ->
                  do send r ReqInc
                     send r Unlock


spawnN :: Int -> Pid -> Process ()
spawnN n p
  | n > 0  = do spawn (client p)
                spawnN (n - 1) p
  | otherwise = return ()
