{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Stutter where
import Control.Process.MessagePassing

main :: Process ()
main = do p <- spawn (stutter 0)
          loop p
  where
    loop :: Pid -> Process ()
    loop p = do send p (Good 0)
                send p (Bad 0)
                loop p

data Message = Good Int | Bad Int
instance RecvMsg Message where
{-@ invariant {v:Message | validMsg v} @-}

stutter :: Int -> Process ()
stutter n = do _ <- recv :: Process Message
               m <- recv :: Process Message
               case m of
                 Good _ -> stutter n
