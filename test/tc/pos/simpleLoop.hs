{-@ LIQUID "--plugin=Control.Process.MessagePassing.PostPlugin" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-eliminate" @-}
{-@ LIQUID "--exactdc" @-}
module Simple where
import Control.Process.MessagePassing

p :: Pid
p = undefined

main :: Process ()
main = do loop ()
          return ()
  where
    loop x = do y <- send p ()
                loop ()
