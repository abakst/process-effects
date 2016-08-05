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
    = do x  <- spawn $ pingProc p
         let i' = myPred i
         xs <- spawnLoop p i'
         let ret = PList x xs
         return ret
  | otherwise
    = return emp
  where
    emp = Emp

pingProc :: Pid -> Process ()
pingProc p
  = do self <- getSelfPid
       let msg = Ping self
       send p msg
       msg' <- recv
       case msg' of
         Pong _ -> return ()

pingLoop :: PidList -> Process ()
pingLoop Emp
  = return ()
pingLoop (PList _ ps)
  = do msg  <- recv
       case msg of
         Ping whom -> pingLoop ps

pongLoop :: PidList -> Process ()
pongLoop Emp
  = return ()
pongLoop (PList p ps)
  = do me <- getSelfPid
       let msg = Pong me
       send p msg
       pongLoop ps

main :: Process ()
main = do me <- getSelfPid
          ps <- spawnLoop me 3 
          pingLoop ps
          pongLoop ps
          return ()
