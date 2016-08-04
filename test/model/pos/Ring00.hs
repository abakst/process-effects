{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Ring where

import Control.Process.MessagePassing
import Data.Either

{-@ invariant {v:Int | validMsg v} @-}

main :: Process ()
main = do me <- getSelfPid
          hd <- spawnRing n me
          send hd n
          ringProc hd
          return ()
  where
    n = 3

ringProc :: Pid -> Process ()
ringProc nxt
  = do send nxt (0 :: Int)

{- spawnRing :: n:Int -> p:Pid -> Process {v:Pid | n = 0 => v = p} @-}
spawnRing :: Int -> Pid -> Process Pid
spawnRing i prev
  = loop i prev
  where
  loop i prev
    | gtZero i
    = do spawn (ringProc prev)
         -- let i' = myPred i
         -- loop i' next
    | otherwise
    = return prev

{-@ myPred :: x:Int -> {v:Int | v = x - 1} @-}
myPred :: Int -> Int
myPred x = x - 1

{-@ gtZero :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
gtZero :: Int -> Bool
gtZero x = x > 0
