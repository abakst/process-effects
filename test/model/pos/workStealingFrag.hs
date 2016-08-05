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

spawnLoop :: Pid -> Int -> Process PidList
spawnLoop p i
    = do x       <- spawn $ workerProc p
         xs      <- spawnLoop p i
         return emp
  where
    emp = Emp

workerProc :: Pid -> Process ()
workerProc master
  = do foo <- go
       return ()
  where
    go :: Process ()
    go 
      = do x <- send master master
           return ()

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
main = do me <- getSelfPid
          let x = 3
          ps <- spawnLoop me x
          return ()
