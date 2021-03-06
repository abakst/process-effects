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

{-@ spawnLoop :: Int -> Process PidList @-}
spawnLoop :: Int -> Process PidList
spawnLoop i 
  | gtZero i
    = do x  <- spawn $ pongProc
         let i' = myPred i
         xs <- spawnLoop i'
         let ret = PList x xs
         return ret
  | otherwise
    = return emp
  where
    emp = Emp

pongProc :: Process ()
pongProc
  = do self <- getSelfPid
       msg <- recv          
       case msg of
         Ping p -> do send p resp
                      return ()
                        where resp = Pong self

pingPong :: PidList -> Process ()
pingPong Emp
  = return ()
pingPong (PList p ps)
  = do self <- getSelfPid
       let msg = Ping self
       send p msg
       resp <- recv
       case resp of
         Pong q -> do pingPong ps
                      return ()

main :: Process Int
main = do ps <- spawnLoop 3 
          pingPong ps
          return 0
