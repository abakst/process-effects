module Cases ( pongProc, Message(..) ) where
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
    Pong q ->
      send q (Ping { ping = myPid })
