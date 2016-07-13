{-# LANGUAGE DeriveAnyClass #-}
module Foo where
import Language.Haskell.MessagePassing

{-@ invariant {v:Int | validMsg v} @-}

{-@ assume p :: {v:Pid | validPid v} @-}
p :: Pid
p = undefined

loop :: Int -> Process ()
loop n
  | n > 0     = do send p n
                   loop z 
  | otherwise = send p n

{-@ qualif Minus1(v:int, x:int): v = x - 1 @-}
