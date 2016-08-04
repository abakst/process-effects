{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module WorkStealing where
import Control.Process.MessagePassing

data PidList = Emp | PList Pid PidList
data Message = Task Int | DONE
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
       go self
       return ()
  where
    go :: Pid -> Process ()
    go self
      = do send master self
           msg <- recv :: Process Message
           case msg of
             Task i -> go self
             DONE   -> return ()

workLoop :: Int -> Process ()
workLoop n
  | gtZero n = do pid     <- recv
                  let msg = Task n
                      n'  = myPred n
                  send pid msg
                  workLoop n'
  | otherwise = return ()

doneLoop :: PidList -> Process ()
doneLoop Emp
  = return ()
doneLoop (PList _ rest)
  = do pid     <- recv
       let msg = DONE
       send pid msg
       doneLoop rest
       return ()

main :: Process ()
main = do me  <- getSelfPid
          ps  <- spawnLoop me numClients
          workLoop numWork
          doneLoop ps
          return ()
  where
    numWork = 4
    numClients = 3
