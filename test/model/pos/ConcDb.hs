{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module ConcDB where

import Control.Process.MessagePassing

data DBAPI = Alloc Int Pid
           | Lookup Int Pid
           | Free
           | Allocated

instance RecvMsg DBAPI
{-@ invariant {v:DBAPI | validMsg v} @-}
{-@ invariant {v:Int   | validMsg v} @-}

data KeyValue = KV Int Int KeyValue
              | Null

main :: Process ()
main = do me <- getSelfPid
          spawn (client me)
          dataBase Null

client :: Pid -> Process ()
client p = do me <- getSelfPid
              send p (Alloc 0 me)
              msg <- recv
              case msg of
                Free      -> send p (0 :: Int)
                Allocated -> return ()

dataBase :: KeyValue -> Process ()
dataBase state
  = do msg <- recv
       case msg of
         Alloc k p  -> handleAlloc k p
         Lookup k p -> handleLookup k p
  where
    handleAlloc :: Int -> Pid -> Process ()
    handleAlloc k p
      = case lookupKey k state of
          Nothing -> do send p Free
                        v <- recv
                        dataBase (KV k v state)
          Just v  -> do send p Allocated
                        dataBase state

    handleLookup :: Int -> Pid -> Process ()
    handleLookup k p = return ()

lookupKey :: Int -> KeyValue -> Maybe Int
lookupKey k Null
  = Nothing
lookupKey k (KV k' v' kv')
  = if k == k' then Just v' else lookupKey k kv'
