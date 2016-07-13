module PingPong ( main, Message(..) ) where
import Language.Haskell.MessagePassing

data Message = Ping { ping :: Pid }
             | Pong { pong :: Pid }
{-@ data Message = Ping { ping :: Pid } | Pong { pong :: Pid } @-}

instance RecvMsg Message where
{-@ invariant {v:Message | validMsg v} @-}
{-@ invariant {v:Integer | validMsg v} @-}

{-@ pongProc :: Process () @-}
pongProc :: Process ()
pongProc = do
  myPid <- getSelfPid
  msg   <- recv
  case msg of
    Ping q ->
      send q (Pong { pong = myPid })

pingProc :: Pid -> Process ()
pingProc p = do
  myPid <- getSelfPid
  let pingMsg = Ping { ping = myPid }
  send p pingMsg
  msg   <- recv
  case msg of
    Pong q -> return ()

main :: Process ()
main = do pong <- spawn pongProc
          pingProc pong
           
