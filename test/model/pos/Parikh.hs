{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Parikh where
import Control.Process.MessagePassing

data ServerAPI = Init Pid Int
               | Set Int
               | Get Pid
               | Bye
               | OK
instance RecvMsg ServerAPI where
{-@ invariant {v:ServerAPI | validMsg v} @-}
{-@ invariant {v:Int | validMsg v} @-}

server :: Process ()
server = do
  init <- recv
  case init of
    Init who s ->
      do send who OK
         serveLoop s
  where
    serveLoop :: Int -> Process ()
    serveLoop t
      = do msg <- recv
           case msg of
             Set t'  -> serveLoop t'
             Get who -> do send who t
                           serveLoop t
             Bye     -> return ()

main :: Process ()
main = do
  me <- getSelfPid
  s  <- spawn server
  send s (Init me 0)
  m1 <- recv
  case m1 of
    OK -> do send s (Set 1)
             send s Bye
