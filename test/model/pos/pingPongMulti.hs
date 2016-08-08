{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Simple where
import Control.Process.MessagePassing

data PidList = Emp | PList Pid PidList
data Message = Ping Pid | Pong Pid
instance RecvMsg Message where
{-@ invariant {v:Pid | validMsg v} @-}
{-@ invariant {v:Int | validMsg v} @-}
{-@ invariant {v:Message | validMsg v} @-}

spawnLoop :: Int -> Process PidList
spawnLoop i 
  | i > 0
    = do x  <- spawn pongProc
         xs <- spawnLoop (i - 1)
         return (PList x xs)
  | otherwise
    = return Emp

pongProc :: Process ()
pongProc
  = do self <- getSelfPid
       msg  <- recv          
       case msg of
         Ping p -> do send p (Pong self)
                      return ()

pingLoop :: PidList -> Process ()
pingLoop Emp
  = return ()
pingLoop (PList p ps)
  = do self <- getSelfPid
       send p (Ping self)
       pingLoop ps
       return ()

waitLoop :: PidList -> Process ()
waitLoop Emp
  = return ()
waitLoop (PList p ps)
  = do resp <- recv
       case resp of
         Pong q -> do waitLoop ps
                      return ()

main :: Process ()
main = do ps <- spawnLoop 2
          pingLoop ps
          waitLoop ps
          return ()
