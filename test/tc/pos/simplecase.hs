{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Simple where
import Control.Process.MessagePassing

data Message = Ping Pid
             | Pong Pid
{-@ data Message = Ping { ping :: Pid } | Pong { pong :: Pid } @-}

instance RecvMsg Message where
{-@ invariant {v:Message | validMsg v} @-}
{-@ invariant {v:Integer | validMsg v} @-}
{-@ invariant {v:Pid | validMsg v} @-}

{-@ main :: Process () @-}
main :: Process () 
main = do p <- spawn $ do msg <- recv
                          case msg of
                            Ping q -> send q m
          self <- getSelfPid
          let msg = Ping self
          send p msg
  where
    m = 0 :: Int
