module Language.Haskell.MessagePassing where

import Control.Monad  
import Control.Exception.Base
{-@ data Process a = P a @-}

{-# ANN type Process "effects" #-}
data Process a = P a
data Pid = Pid Int
         deriving Eq

class RecvMsg a where                  

instance RecvMsg () where
instance RecvMsg Int where
instance RecvMsg Char where
instance RecvMsg Pid where
instance RecvMsg a => RecvMsg [a] where  

instance Functor Process where
instance Applicative Process where
instance Monad Process where  
  (>>=) = bind

{-@ 
measure validPid :: Pid -> Prop
validPid(Pid x) = true
@-}
{- 
measure validMsg :: a -> Prop
validMsg x = true
-}
validMsg :: a -> Bool
validMsg x = True
{-@ measure validMsg :: a -> Prop @-}

{-@ invariant {v:Pid | validPid v} @-}

{-@ assume undefined :: Process a  -> (a -> Process b) -> Process b @-}
bind :: Process a -> (a -> Process b) -> Process b
bind = undefined

{-# ANN send "p:0 -> m:0 -> { \\p.(\\m.(\\$K.\\me. send me p m >>= $K)) }" #-}
{-@ send :: forall <q :: m -> Prop>.
            { x :: m<q> |- m<q> <: {v:m | validMsg v} }
            {v:Pid | validPid v} -> m:m<q> -> Process () 
@-}
send :: Pid -> m -> Process ()
send p m = undefined

{-# ANN recv "{ \\$K.\\me. recv me >>= $K }" #-}
{-@ recv :: RecvMsg m => Process m @-}
recv :: RecvMsg m => Process m
recv = undefined

{-# ANN getSelfPid "{ \\$K.\\me. ($K me) }" #-}
{-@ getSelfPid :: Process {v:Pid | validPid v} @-}
getSelfPid :: Process Pid
getSelfPid = undefined

{-# ANN spawn "forall $e. { $e } -> { \\p.(\\$K.\\me.([x]( $e (done x) x | $K x ))) }" #-}
{-@ spawn :: Process () -> Process Pid @-}
spawn :: Process () -> Process Pid
spawn = undefined

{-# ANN spawnMany "forall $e. n:0 -> { $e } -> { \\n.\\p.(\\$K.\\me.([x:n]( $e (done x) x | $K x ))) }" #-}
spawnMany :: Int -> Process () -> Process Pid        
spawnMany = undefined

{-# ANN exec "forall $e. { $e } -> 0" #-}
exec :: Process () -> ()
exec = undefined

fix :: (a -> a) -> a
fix = undefined
