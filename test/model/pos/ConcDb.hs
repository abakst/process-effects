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

data KeyValue = KV Int Int KeyValue
              | Null

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
                        dataBase state

    handleLookup :: Int -> Pid -> Process ()
    handleLookup k p = return ()

lookupKey :: Int -> KeyValue -> Maybe Int
lookupKey k Null
  = Nothing
lookupKey k (KV k' v' kv')
  = if k == k' then Just v' else lookupKey k kv'
