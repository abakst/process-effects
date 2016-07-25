{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module PingPong ( main, Message(..) ) where
import Control.Process.MessagePassing

data Message = Ping Pid
             | Pong Pid

instance RecvMsg Message where
{-@ invariant {v:Message | validMsg v} @-}
{-@ invariant {v:Integer | validMsg v} @-}

{-@ pongProc :: Process () @-}
pongProc :: Process ()
pongProc = do
  myPid <- getSelfPid
  msg   <- recv
  case msg of
    Ping q -> do
      let response = Pong myPid
      send q response 

pingProc :: Pid -> Process ()
pingProc p = do
  myPid <- getSelfPid
  let pingMsg = Ping myPid
  send p pingMsg
  msg   <- recv
  case msg of
    Pong q -> return ()

main :: Process ()
main = do pong <- spawn pongProc
          pingProc pong
           
