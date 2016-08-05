{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
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
{-@ invariant {v:() | validMsg v} @-}

-- main :: Process ()
-- main = do me <- getSelfPid
--           spawnN n me
--           resServer
--   where
--     n = 3 :: Int

foo = do x <- recv
         case x of
           Lock p -> send p ()

-- resServer :: Process ()
-- resServer = resLoop unlk
--   where
--     unlk = Unlocked
--     lk   = Locked
--     resLoop x
--       = case x of
--           Unlocked ->
--             do lock <- recv
--                case lock of
--                  Lock p ->
--                   do send p Acquired
--                      resLoop Locked
          -- Locked ->
          --   do request <- recv
          --      case request of
          --        ReqInc -> resLoop lk
          --        ReqGet -> resLoop lk
          --        Unlock  -> resLoop unlk

-- client :: Pid -> Process ()
-- client r = do me <- getSelfPid
--               let lock_msg = Lock me
--               send r lock_msg
--               msg <- recv
--               case msg of
--                 Acquired ->
--                   do send r inc
--                      send r unlock
--   where
--     lock me = Lock me
--     unlock  = Unlock
--     inc     = ReqInc


-- spawnN :: Int -> Pid -> Process ()
-- spawnN n p
--   | gtZero n  = do spawn (client p)
--                    let n' = myPred n
--                    spawnN n' p
--   | otherwise = return ()

-- {-@ myPred :: x:Int -> {v:Int | v = x - 1} @-}
-- myPred :: Int -> Int
-- myPred x = x - 1

-- {-@ gtZero :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
-- gtZero :: Int -> Bool
-- gtZero x = x > 0
