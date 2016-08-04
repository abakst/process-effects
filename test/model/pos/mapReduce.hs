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

{-@ myPred :: x:Int -> {v:Int | v = x - 1} @-}
myPred :: Int -> Int
myPred x = x - 1

{-@ gtZero :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
gtZero :: Int -> Bool
gtZero x = x > 0

{-@ spawnLoop :: Pid -> Int -> Process PidList @-}
spawnLoop :: Pid -> Int -> Process PidList
spawnLoop p i
  | gtZero i
    = do x       <- spawn (workerProc p)
         let i'  = myPred i
         xs      <- spawnLoop p i'
         let ret = PList x xs
         return ret
  | otherwise
    = return emp
  where
    emp = Emp

workerProc :: Pid -> Process ()
workerProc master
  = do self <- getSelfPid
       foo  <- go self
       return ()
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
  | gtZero n = do pid     <- recv
                  let msg = Task n p
                      n'  = myPred n
                  send pid msg
                  workLoop p n'
                  return ()
  | otherwise = return ()

doneLoop :: Int -> Process ()
doneLoop n
  | gtZero n = do pid     <- recv
                  let msg = DONE
                      n'  = myPred n
                  send pid msg
                  doneLoop n'
                  return ()
  | otherwise = return ()

masterLoop :: Int -> Process ()              
masterLoop i
  | gtZero i = do x <- recv :: Process Int
                  let i' = myPred i
                  masterLoop i'
                  return ()
  | otherwise = return ()

main :: Process ()
main = do me <- getSelfPid
          queue <- spawn $ do n <- recv
                              workLoop me numWork
                              doneLoop n
                              return ()
          ps <- spawnLoop queue numClients
          send queue numClients
          masterLoop numWork
          return ()
  where
    numWork = 2
    numClients = 3
