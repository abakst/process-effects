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
          hd <- spawnRing 3 me
          send hd (0 :: Int)
          ringProc 0 hd

ringProc :: Int -> Pid -> Process ()
ringProc t nxt
  = do msg <- recv :: Process Int
       if msg > t then
         do send nxt msg
            ringProc msg nxt
       else
         if msg < t then
           ringProc t nxt
         else do
           send nxt msg
           return ()

spawnRing :: Int -> Pid -> Process Pid
spawnRing i prev
  = loop i prev
  where
  loop i x
    | i > 0
    = do x' <- spawn (send x i >> ringProc i x)
         loop (i - 1) x'
    | otherwise
    = return x

{-@ myPred :: x:Int -> {v:Int | v = x - 1} @-}
myPred :: Int -> Int
myPred x = x - 1

{-@ gtZero :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
gtZero :: Int -> Bool
gtZero x = x > 0

{-@ lt :: x :Int -> y:Int -> {v:Bool | Prop v <=> x < y} @-}
lt :: Int -> Int -> Bool
lt x y = x < y
{-@ gt :: x :Int -> y:Int -> {v:Bool | Prop v <=> y < x} @-}
gt :: Int -> Int -> Bool
gt x y = x > y
