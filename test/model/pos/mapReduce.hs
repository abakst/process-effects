{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module WorkStealing where
import Control.Process.MessagePassing

data PidList = Emp | PList Pid PidList
data Message = Task Int Pid | DONE
instance RecvMsg Message where
{-@ invariant {v:Pid | validMsg v} @-}
{-@ invariant {v:Int | validMsg v} @-}
{-@ invariant {v:Message | validMsg v} @-}

{-@ spawnLoop :: Pid -> Int -> Process PidList @-}
spawnLoop :: Pid -> Int -> Process PidList
spawnLoop p i
  | i > 0
    = do x       <- spawn (workerProc p)
         xs      <- spawnLoop p (i - 1)
         return (PList x xs)
  | otherwise
    = return Emp

workerProc :: Pid -> Process ()
workerProc master
  = do self <- getSelfPid
       go self
  where
    go :: Pid -> Process ()
    go self
      = do send master self
           msg <- recv :: Process Message
           case msg of
             Task i p -> do send p i
                            go self
                            return ()
             DONE   -> return ()
           return ()

workLoop :: Pid -> Int -> Process ()
workLoop p n
  | n > 0    = do pid     <- recv
                  send pid (Task n p)
                  workLoop p (n - 1)
                  return ()
  | otherwise = return ()

doneLoop :: Int -> Process ()
doneLoop n
  | n > 0    = do pid     <- recv
                  let msg = DONE
                  send pid msg
                  doneLoop (n - 1)
                  return ()
  | otherwise = return ()

masterLoop :: Int -> Process ()              
masterLoop i
  | i > 0    = do _ <- recv :: Process Int -- Could do something with this...
                  masterLoop (i - 1)
                  return ()
  | otherwise = return ()

main :: Process ()
main = do me <- getSelfPid
          -- Spawn a work queue that waits for
          -- `numWork + numClients` requests
          queue <- spawn $ do n <- recv
                              workLoop me numWork
                              doneLoop n
                              return ()
          ps <- spawnLoop queue numClients

          -- Tell the queue about the clients
          send queue numClients

          -- Wait for responses
          masterLoop numWork

          return ()
  where
    numWork = 2
    numClients = 2
