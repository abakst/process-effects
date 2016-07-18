{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Simple where
import Control.Process.MessagePassing

data PidList = Emp | PList Pid PidList
{-@ invariant {v:Pid | validMsg v} @-}
{-@ invariant {v:Int | validMsg v} @-}
{-@ myPred :: x:Int -> {v:Int | v = x - 1} @-}
myPred :: Int -> Int
myPred x = x - 1

{-@ gtZero :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
gtZero :: Int -> Bool
gtZero x = x > 0            

{-@ spawnLoop :: x:{v:Int | true } -> Process PidList @-}
spawnLoop :: Int -> Process PidList
spawnLoop i 
  | gtZero i
    = do x  <- spawn $ do i <- recv :: Process Int
                          return ()
         let i' = myPred i
         xs <- spawnLoop i'
         let ret = PList x xs
         return ret
  | otherwise
    = return emp
  where
    emp = Emp

main :: Process Int
main = do ps <- spawnLoop 3 
          z  <- sendLoop ps
          return 0

{-@ zero :: {v:Int | v = 0} @-}
zero :: Int
zero = 0

sendLoop :: PidList -> Process ()
sendLoop arg =
  case arg of
    Emp        -> return ()
    PList x xs -> do send x zero
                     sendLoop xs
                     return ()
