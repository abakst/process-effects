module spec Language.Haskell.MessagePassing where

measure validPid :: Pid -> Prop
measure validMsg :: a -> Prop

invariant {v:Pid | validPid v}

assume recv
    :: (Language.Haskell.MessagePassing.RecvMsg m) => (Language.Haskell.MessagePassing.Process m)

    
assume send
    :: forall <q :: m -> Prop>.
              { x :: m<q> |- m<q> <: {v:m | validMsg v} }
              {v:Language.Haskell.MessagePassing.Pid | validPid v} -> m:m<q> -> Language.Haskell.MessagePassing.Process () 
