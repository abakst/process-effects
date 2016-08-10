{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module FireWall where
import Control.Process.MessagePassing

data PidList = Emp | PList Pid PidList
data Message = Call Pid Int
             | Answer Int
             | BadReq
{-@ invariant {v:Message | validMsg v} @-}
instance RecvMsg Message where

main :: Process ()
main = do srv <- spawn (server floog)
          fir <- spawn (server (firewall srv))
          me  <- getSelfPid
          -- send fir (Call me 1)
          send srv (Call me 0)
          return ()

floog :: Int -> Process Message
floog x = return $ Answer (x + 1)

server :: (Int -> Process Message) -> Process ()
server h
  -- = h 0 >> return ()
  -- = return ()
  = do call <- recv
       case call of
         Call p i -> do resp <- h i
                        send p resp

firewall :: Pid -> Int -> Process Message
firewall p x
  | x /= 0
  = do me <- getSelfPid
       send p (Call me x)
       recv
  | otherwise
  = return BadReq
