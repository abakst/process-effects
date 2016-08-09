{-# Language ViewPatterns #-}
{-# Language TypeSynonymInstances #-}
{-# Language FlexibleInstances #-}
module Control.Process.MessagePassing.Promela where

import           Debug.Trace
import           Type
import           Name
import           TyCon
import           DataCon
import           Unique
import           TysWiredIn
import           PrelNames
import           Control.Monad.State
import           Text.Printf
import           Data.List
import           Data.Maybe
import           Data.Generics hiding (TyCon, empty)
import           Data.Function
import qualified Data.Map.Strict as M
import qualified Language.Fixpoint.Types as Fp
import qualified Language.Haskell.Liquid.Types as R
import           Text.PrettyPrint.HughesPJ hiding ((<$>))
import           Control.Process.MessagePassing.EffectTypes
import           Control.Process.MessagePassing.PrettyPrint

tracepp :: Pretty a => String -> a -> a
tracepp msg x = trace (msg ++ " " ++ render (pretty x)) x

debug :: Show a => String -> a -> a
debug msg x = trace (msg ++ ": " ++ show x) x

debugEff :: String -> Effect -> Effect
debugEff msg x = trace (msg ++ ": " ++ render (pretty x)) x

class Promela a where
  promela :: a -> Doc

instance Promela EffTy where
  promela (EffTerm e)
    = promelaProgram 10 closed
    where
      closed =
        debugEff "closed"  $
        betaReduce
          (AppEff (AppEff e doneEff) (EffVar (Src (symbol "_init") Nothing)))
      doneEff = AbsEff (Src (symbol "_done") Nothing) (AppEff (EffVar (Src (symbol "done") Nothing)) (EffVar (Src (symbol "_init") Nothing)))
  promela _
    = error "I only know how to convert values of type { λK.λme.x }!"

initialPid :: Symbol
initialPid = symbol "_init"
pidCtrName = symbol "_pidCtr"

retVar :: Symbol
retVar  = symbol "_ret"

maxProcsVar :: Symbol
maxProcsVar = symbol "max_procs"

procName :: Symbol -> Doc
procName s = promela s <> text "proc"

sendDef :: Doc
sendDef = text "#define send(whom,ty,msg)" <+>
          text "assert(whom.p);"           <+>
          text "mbuf[_pid*max_procs + whom.v]!ty,msg"

recvDef :: Doc
recvDef = text "#define recv(i,ty,msg) mbuf[i*max_procs + _pid]??ty,msg"

assumeDef :: Doc
assumeDef = text "#define assume(_p) do :: _p -> break :: else -> skip od"

stackSize = text "STACKSZ"
heapSize  = text "HEAPSZ"

heapSizeDef :: Doc
heapSizeDef = text "#ifndef HEAPSZ"    $+$
              text "#define HEAPSZ 16" $+$
              text "#endif"

stackSizeDef :: Doc
stackSizeDef = text "#ifndef STACKSZ"    $+$
              text "#define STACKSZ 16" $+$
              text "#endif"

valTypeDef :: Doc
valTypeDef = text "typedef val {" <+>
             text "bit" <+> validBit <> semi <+>
             intType    <+> valueField <> semi <+>
             text "}" <> semi
baseVals = vcat [ ptrType <+> v <> semi | v <- [unitVal, trueVal, falseVal] ]

unitVal  = text "unit"
trueVal  = text "true_val"
falseVal = text "false_val"

true  = text "true"
false = text "false"

initializeBaseVals = d_step $
  assnField validBit    unitVal true <> semi $+$
  assnField valueField  unitVal true <> semi $+$

  assnField validBit    trueVal true <> semi $+$
  assnField valueField  trueVal true <> semi $+$

  assnField validBit    falseVal true <> semi $+$
  assnField valueField  falseVal false <> semi

promelaProgram :: Int -> Effect -> Doc
promelaProgram n eff
  = maxProcs            $+$
    sendDef             $+$
    recvDef             $+$
    assumeDef           $+$
    heapSizeDef         $+$
    stackSizeDef        $+$
    mtype               $+$
    valTypeDef          $+$
    baseVals            $+$
    types               $+$
    records             $+$
    heaps               $+$
    buf                 $+$
    pidCtr              $+$
    children            $+$
    initialProc master
  where
    (master, st)
      = runState (promelaEffect eff) emptyPState { proc_limit = n }
    children
      = promelaProcs st
    records
      = recordTypes st
    maxProcs = text "#define" <+> promela maxProcsVar <+> int n

    mtype  = declMtype allts
    types  = vcat $ declareType <$> tinfos
    cinfos = concatMap cinfo tinfos
    allts  = nub (tyInfos (snd <$> boundTys eff))
    tinfos = [t | t@TypeInfo {} <- allts]
    heaps  = vcat $ goHeap  <$> tinfos
    goHeap ti = heapDecl (tyname ti)
    pidCtr = intType <+> promela pidCtrName
         <+> equals <+> int 1 <> semi

    -- N channels --
    numChans = n*n
    buf      = chanDecl numChans n

bodyTemplate body
  = nest 2 (ret $+$ body)
    where
      ret = ptrType <+> (promela retVar) <> semi

promelaProcs :: PState -> Doc
promelaProcs st
  = vcat (go <$> procs st)
  where
    go (name, args, body)
      = text "proctype" <+> procName name <+> formalsList args <+> text "{" $+$
          bodyTemplate body $+$
        text "}"

recordTypes :: PState -> Doc
recordTypes PState { rec_funs = recs }
  = vcat $ go <$> recs
  where
    go (x,f,fs,ls)
      =  text "typedef" <+> actRecordTyName f $+$
         braces (vcat (pcField : fields))
      where
        recs = (promela . symbol <$> fs) ++ (promela <$> ls)
        pcField = intType <+> pcRecord <> semi
        fields  = [ ptrType <+> a <> semi | a <- recs ]

initialProc d =
  text "active proctype master() {" $+$
  initializeBaseVals $+$
  bodyTemplate (initDecl $+$ d) $+$
  text "}"
  where
    initDecl = ptrType <+> promela initialPid <> semi                           $+$
               promela initialPid `dot` validBit <+> equals <+> true <> semi    $+$
               promela initialPid `dot` valueField <+> equals <+> int 0 <> semi

declMtype tinfos
  = text "mtype" <+> braces (hcat $ punctuate comma mtypes)
  where
    mtypes  = go <$> tinfos
    go ti   = promela (tyname ti) <> text "_ty"

chanDecl n sz
  = text "chan mbuf" <> brackets (int n) <+>
    equals <+> brackets (int sz) <+> text "of" <+>
    braces (text "mtype" <> comma <> ptrType) <> semi

chanName :: Fp.Symbol -> Doc
chanName t = promela t <> text "_chan"

ptrType :: Doc
ptrType = text "val"

intType :: Doc
intType = text "byte"

objIdType :: Doc
objIdType = text "byte"

tableDecl :: Int -> TypeInfo -> Doc
tableDecl n ti
  = ptrType <+> tableName ti <> brackets (int n) <> semi

heapDecl :: Fp.Symbol -> Doc
heapDecl ti
  = promela ti <+> heapName ti <> brackets heapSize <> semi $+$
    intType <+> heapPtrName ti <+> equals <+> int 0 <> semi

tableName :: TypeInfo -> Doc
tableName ti = promela (tyname ti) <> text "_table"

heapName :: Fp.Symbol -> Doc
heapName ty = promela ty <> text "_heap"

heapPtrName :: Fp.Symbol -> Doc
heapPtrName ty = promela ty <> text "_heap_ptr"

data SrcPattern = InitDecl Fp.Symbol (Maybe Type) Doc
                | Send Effect Effect

instance Promela Fp.Symbol where
  promela s = promela (symbolString s)

instance Promela String where
  promela s = text (cleanup <$> s)
    where
      cleanup = replace '.' '_'
              . replace '#' '_'
              . replace '$' '_'
              . replace '\'' '_'
              . replace '(' 't'
              . replace ')' 't'
      replace x y c = if c == x then y else c

data PState = PState {
    vars       :: [Fp.Symbol]
  , procs      :: [(Fp.Symbol, [Fp.Symbol], Doc)]
  , rec_funs   :: [(Fp.Symbol, Fp.Symbol, [Binder], [Fp.Symbol])]
  , rec_stack  :: [(Fp.Symbol, Fp.Symbol, Int, Doc)]
  , rec_label  :: [(Fp.Symbol, Int)]
  , rec_ctxt   :: [Fp.Symbol]
  , proc_limit :: Int
  , n          :: Int
  }
type PM a = State PState a

actRecordTyName :: Fp.Symbol -> Doc
actRecordTyName x
  = promela x <> text "_rec"

stackPtrName :: Fp.Symbol -> Doc
stackPtrName x
  = promela x <> text "_ptr"

pcRecord :: Doc
pcRecord = text "_pc"

stackName :: Fp.Symbol -> Doc
stackName x
  = promela x <> text "_stack"

emptyPState :: PState
emptyPState = PState { vars       = [initialPid]
                     , procs      = []
                     , n          = 0
                     , rec_ctxt   = []
                     , rec_stack  = []
                     , rec_label  = []
                     , rec_funs   = []
                     , proc_limit = 5
                     }

atomic :: Doc -> Doc
atomic d
  = text "atomic" <+> braces d

d_step :: Doc -> Doc
d_step d
  = text "d_step" <+> braces d

incPidCtr = promela pidCtrName <> text "++" <> semi $+$
            promelaMacro "assert" [ promela pidCtrName <+>
                                    text "<" <+>
                                    promela maxProcsVar
                                  ]

promelaEffect :: Effect -> PM Doc
promelaEffect e = do recCall <- maybeRecursiveCall e
                     go recCall e
  where
    go (Just (x, f, xs, ls, as)) _
      = promelaRecursiveCall x f xs ls as
    go _ (Pend e i)
      = do env <- promelaInfo i
           k   <- promelaEffect e
           return (env $+$ k)
    go _ (maybeSend -> Just (p,m))
      = promelaSend p m
    go _ (maybeRecursive -> Just (x, bdy, (fs,as), k, me))
      = promelaRecursive x bdy (fs,as) k me
    go _ (Nu x (Par e1 e2))
      = promelaNu x e1 e2
    go _ (Bind m (AbsEff (Src x t) n))
      = promelaBind m (x,t) n
    go _ (Bind m g)
      = error (printf "What %s\n" (render (pretty g)))
    go _ (NonDet es)
      = do e <- promelaInfo i
           k <- promelaNonDet es
           return (e $+$ k)
      where
        i = head [ i | (Assume i _ _) <- es ]
    go _ (Assume i unfolds e)
      = promelaAssume i unfolds e
    go _ (AppEff (EffVar (Src f _)) _)
      | symbolString f == "done"
      = return $ text "true"
      | symbolString f == "die"
      = return $ text "assert (0 == 1)"
    go _ (EffVar (Src f _))
      = promelaVar f
    go c (EffVar (Eff f))
      = returnStack
    go _ (AppEff (EffVar (Eff f)) e)
      = do vs            <- gets vars
           retStack      <- returnStack
           let (x, _, d) = promelaVal vs e
           modify $ \s -> s { vars = validVars (x : vs) }
           return $ fromMaybe empty d $+$ setReturn x $+$ retStack
      where
        setReturn x
          | symbolString x /= "_"
          = promela retVar `copyVal` promela x <> semi
          | otherwise
          = empty
    go _ e = error (render $ text "promelaEffect:" <+> pretty e)


copyVal x y = d_step $ vcat [ copyField f x y <> semi | f <- [validBit, valueField] ]

returnStack :: PM Doc
returnStack
  = do stack <- gets rec_ctxt
       return $ case stack of
                  f:_ -> stackPtrName f <> text "--" <> semi

maybeReturn :: Effect -> Maybe (Fp.Symbol, Maybe Effect)
maybeReturn (EffVar (Eff f))
  = Just (f, Nothing)
maybeReturn (AppEff (EffVar (Eff f)) e)
  = Just (f, Just e)

argList :: [Fp.Symbol] -> Doc
argList = parens . hcat . punctuate comma . fmap promela

formalsList :: [Fp.Symbol] -> Doc
formalsList = parens . hcat . punctuate semi . fmap go
  where
    go s = ptrType <+> promela s

validVars = nub . filter (\v -> symbolString v /= "_")

promelaInfo :: Info -> PM Doc
promelaInfo i@(Info x ty φ γ) -- yes unicode. sue me.
  = do env <- gets vars
       let (ds0,env0) = foldr go ([],env) $ [ (Fp.symbol x',t)
                                            | (x', Just t) <- bs
                                            , x /= Fp.symbol x'
                                            ]
           bs      = M.toList γ
           (z,_,d) = promelaVal env0 (Pend (EffVar (Src x (Just ty))) i)
           ds      = ds0 ++ if x `notElem` env then [d] else []
           envdoc  = pretty i
       modify $ \s -> s { vars = maybe env0 (const (validVars $ (z : env0))) d }
       case catMaybes ds of
         [] -> return empty
         xs -> return $ text "/*" $+$ envdoc $+$ text "*/" $+$ foldl1 ($+$) xs
  where
    go (x,t) (docs, xs)
      | x `notElem` xs, Just (z,Just d) <- bindVal xs (x,t)
      = (Just d:docs, x:xs)
      | otherwise
      = (docs, xs)
    bindVal xs (x,t)
      | Just ty <- extractTy t
      = let (z,_,d) = promelaVal xs (pendBind ty (Fp.tracepp "x ==>" x,t))
        in Just (z,d)
      | otherwise
      = Nothing
    extractTy :: R.SpecType -> Maybe Type
    extractTy t@(R.RApp (R.RTyCon{R.rtc_tc = c}) _ _ _)
      | null (tyConDataCons c)
      = Nothing -- error (printf "extractTy: TBD %s" (Fp.showpp t))
      | otherwise
      = Just (dataConOrigResTy . head $ tyConDataCons c)
    extractTy (R.RAppTy{R.rt_arg = a})
      = extractTy a
    extractTy t
      = Nothing
    pendBind ty (x,t)
      = Pend (EffVar (Src x (Just ty))) (infoBind ty (x,t))
    infoBind ty (x,t)
      = Info x ty t γ

makeNonDet ds
  = text "if" $+$ nest 2 (vcat ds') $+$ text "fi"
  where
    ds' = (text "::" <+>) <$> ds

promelaNonDet es
  = do ds <- mapM go es
       let promDs = makeNonDet ds
       return promDs
  where
    go e = do vs <- gets vars
              d <- promelaEffect e
              modify $ \s -> s { vars = vs }
              return d

promelaAssume i@(Info x ty reft g) (c,ys) e
  | PrimType {tyname = t} <- tyInfo ty,
    (Just d) <- maybeCompare i
  = do env <- promelaInfo i
       e' <- promelaEffect e
       let x = if getUnique c == trueDataConKey
               then d else text "!" <> parens d
       return $ env $+$ x <+> text "->" <+> braces e'
promelaAssume (Info x ty reft g) (c,ys) e
  = do vs <- gets vars
       modify $ \s -> s { vars = validVars ys ++ vs }
       d <- promelaEffect e
       return $ assm vs $+$ nest 2 (braces (decls vs $+$ d))
  where
    dcname      = symbol (dataConWorkId c)
    tag         = int . ctag $ fromMaybe err (cstrFor dcname ty)
    err         = error $ (printf "*****\nCan't find info for %s\n*****" (symbolString dcname))
    decls vs    = vcat (decl vs <$> (zip [0..] ys))
    assm vs
      | x `elem` vs
      = obj t x <> text ".tag" <+> equals <> equals <+> tag <+> text "->"
      | otherwise
      = text "/*" <+> promela x <+> vcat (punctuate (text ", ") (promela <$> vs)) <+> text "*/" <+> true
    decl  vs (i,y)  = ptrType <+> promela y <> semi $+$ unfold vs (i,y)
    unfold vs (i,y)
      | x `elem` vs
      = copyVal (promela y) (obj t x `dot` (text "c" <> tag <> brackets (int i))) <> semi
      | otherwise
      = assnField validBit (promela y) false
    t = tyname (tyInfo ty)

maybeCompare :: Info -> Maybe Doc
maybeCompare (Info x ty (R.rTypeReft -> reft) g)
  = case extractPropPreds go reft of
      (xs, c):_ -> Just (ifValid xs c)
      _   -> Nothing
  where
    ifValid ys c = foldl goValid c ys
    goValid c y  = c <+> text "||" <+> text "!" <+> promela y `dot` validBit
    go (Fp.PAtom o e1 e2) = do (xs1, e1') <- go e1
                               (xs2, e2') <- go e2
                               o'  <- goOp o
                               return $ (nub (xs1 ++ xs2), parens (e1' <+> o' <+> e2'))
    go (Fp.EVar x)        = Just $ ([x], promela x `dot` valueField)
    go (Fp.ECon (Fp.I i)) = Just $ ([], int (fromInteger i))
    go _ = Nothing
    goOp (Fp.Eq) = Just $ equals <> equals
    goOp (Fp.Ne) = Just $ text "!" <> equals
    goOp (Fp.Gt) = Just $ text ">"
    goOp (Fp.Lt) = Just $ text "<"
    goOp (Fp.Ge) = Just $ text ">="
    goOp (Fp.Le) = Just $ text "<="
    goOp _ = Nothing

promelaNu :: Fp.Symbol -> Effect -> Effect -> PM Doc
promelaNu c e1 e2
  = do vs <- gets vars
       let args = if c `notElem` vs then c : vs else vs
       modify $ \s -> s { vars = args }
       p <- promelaEffect e1
       modify $ \s -> s { vars = args }
       d <- promelaEffect e2
       modify $ \s -> s { vars = args
                        , procs = (c, args, p) : procs s
                        }
       let decl = if c `notElem` vs then
                    ptrType <+> promela c <> semi
                  else
                    empty
       return $
         decl $+$
         d_step (
           promela c `dot` validBit   <+> equals <+> true <> semi $+$
           promela c `dot` valueField <+> equals <+> promela pidCtrName <> semi $+$
           incPidCtr
         ) $+$
         text "run" <+> procName c <> argList args <> semi $+$
         d

promelaBind :: Effect -> (Fp.Symbol, Maybe Type) -> Effect -> PM Doc
promelaBind (Pend e1 i@(Info _ _ _ g)) (x,t) e2
  = do env <- promelaInfo i
       let f = Fp.tracepp "Gamma" <$> g
       k   <- f `seq`  promelaBind e1 (x,t) e2
       return (env $+$ k)
promelaBind e1 (x,t) e2
  | Just (p,m) <- maybeSend e1
  = do d1 <- promelaSend p m
       d2 <- promelaEffect e2
       return $ (d1 <> semi $+$ d2)
  | Just p <- maybeRecv e1
    = promelaRecv p (x,t) e2
promelaBind (AppEff (EffVar (Src f _)) (EffVar (Src v _))) (x,t) e2
  | symbolString f == "return"
  = do vs <- gets vars
       modify $ \s -> s { vars = validVars (x : vs) }
       k <- promelaEffect e2
       return (if x `notElem` vs then ptrType else empty <+> promela x <+> equals <+> promela v $+$ k)
promelaBind e1 (x,t) e2
  = error (printf "promelaBind: %s" (render $ pretty (Bind e1 (AbsEff (Src x t) e2))))

promelaRVal :: Effect -> Doc
promelaRVal e
  = error (printf "rval: %s" (render $ pretty e))

promelaMacro f args
  = text f <> parens (hcat $ punctuate comma args)

promelaRecv :: Fp.Symbol -> (Fp.Symbol, Maybe Type) -> Effect -> PM Doc
promelaRecv p (x, Just t) e2
  = do n    <- gets proc_limit
       decl <- maybeDecl x
       modify $ \s -> s { vars = validVars (x : vars s) }
       d    <- promelaEffect e2
       return (decl $+$ recv n <> semi $+$ d)
  where
    recv n  = atomic $ makeNonDet (recv1 <$> [0..n-1])
    recv1 i = promelaMacro "recv" [ int i
                                  , ty
                                  , promela x
                                  ]
    ty    = case tinfo of
              PrimType { tyname = n } -> promela n <> text "_ty"
              _                       -> promela t
    tinfo = tyInfo t

maybeDecl :: Fp.Symbol -> PM Doc
maybeDecl x
  | symbolString x == "_"
  = return empty
  | otherwise
  = do vs <- gets vars
       if x `notElem` vs then
         return (ptrType <+> promela x <> semi)
       else
         return empty

promelaSend :: Effect -> Effect -> PM Doc
promelaSend p m
  = do vs                   <- gets vars
       let (xP, _,  decls)  = promelaVal vs p
           (xM, ty, decls') = promelaVal vs m
           vs'              = validVars ([xP, xM] ++ vs)
           spawnCmd         = promelaMacro "send" [ promela xP
                                                  , promela ty
                                                  , promela xM
                                                  ]
       modify $ \s -> s { vars = vs' }
       return $ (maybe empty    ($+$ empty)    decls) $+$
                (maybe spawnCmd ($+$ spawnCmd) decls')

-- This is the initial call to a recursive function.
-- Need to create a stack, set up first activation record,
-- then render the body of the function
promelaRecursive x bdy (fs,as) (AbsEff ret@(Src r _) k) me
  = do vs           <- gets vars
       i            <- gets n
       labels       <- gets rec_label
       let f        = symbol ("fun" ++ show i)
           locals   = localVars bdy
       modify $ \s -> s { rec_funs = (x,f,fs,locals):rec_funs s
                        , n = i + 1
                        , vars = locals ++ (symbol <$> fs) ++ vs
                        , rec_label = (x,0):rec_label s
                        , rec_ctxt = f : rec_ctxt s
                        }
       oldchunks    <- gets rec_stack
       body         <- promelaEffect bdy
       modify $ \s -> s { vars = vs
                        , rec_label = labels
                        , rec_ctxt = tail (rec_ctxt s)
                        }
       chunks       <- gets rec_stack

       let myChunks = [ (i,d) | (k,_,i,d) <- chunks, k == x ]
           pcEq i   = pcRecord <+> equals<>equals <+> int i
           -- pcEq i   = stackFrame f <> text "." <> pcRecord <+> equals<>equals <+> int i
           goChunk (i,d) = text "::" <+> pcEq i <+> text "->" $+$
                           nest 2 (braces d)

           declStack    = (actRecordTyName f) <+> stackName f <> brackets stackSize <> semi
           declStackPtr = intType <+> stackPtrName f <+> equals <+> int 1 <> semi
           declLocals   = vcat [ ptrType <+> promela (symbol x) <> semi | x <- locals ]
           declFormals  = vcat [ ptrType <+> promela (symbol f) <> semi | f <- fs ]

           loopBody = popActivationRecord f locals (symbol <$> fs)  $+$
                      text "if" $+$
                        (nest 2 $ vcat (goChunk <$> ((0,body):myChunks))) $+$
                      text "fi"

           loop = text "do"   $+$
                    nest 2 (text "::" <+> stackPtrName f <+> equals <> equals <+> int 0
                             <+> text "-> break") $+$
                    nest 2 (text ":: else ->" <+> braces loopBody) $+$
                  text "od"

           (argXs, push) =
             pushArgs vs f [] (symbol <$> fs) as 0

           call = declStack    $+$
                  declStackPtr $+$
                  declLocals   $+$
                  declFormals  $+$
                  push         $+$
                  loop
       modify $ \s -> s { vars = validVars (r : argXs ++ vars s) }
       kont <- promelaEffect k
       modify $ \s -> s { rec_stack = oldchunks }
       return $ call                      $+$
                promelaMaybeDecl r retVar $+$
                kont

promelaMaybeDecl x y
  = if symbolString x /= "_" then
      ptrType <+> promela x <> semi $+$
      copyVal (promela x) (promela y) <> semi
    else
      empty

promelaRecursiveDef x bdy xs vs
  = do i     <- gets n
       let f = symbol ("fun" ++ show i)
       modify $ \s -> s { n    = i + 1
                        , vars = validVars (xs ++ vs)
                        }
       bdy'   <- promelaEffect (dropArgs bdy)
       modify $ \s -> s { vars = vs }
       return (x,f,Just bdy')
  where
    dropArgs (AbsEff x e) = dropArgs e
    dropArgs e            = e
    replaceBody x bdy r@(x',f,xs,vs,_)
      | x == x'   = (x',f,xs,vs,Just bdy)
      | otherwise = r

promelaRecursiveCall :: Fp.Symbol -> Fp.Symbol -> [Binder] -> [Fp.Symbol] -> [Effect] -> PM Doc
promelaRecursiveCall xf f forms ls as
  = do l <- newLabel xf
       vs <- gets vars
       let place   =
             stackPtrName f <> text "++" <> semi $+$
             saveLocals f ls (symbol <$> forms) args l <> semi $+$
             push <> semi
           push    = snd $ pushArgs vs f ls (symbol <$> forms) args l
       modify $ \s -> s { vars = maybe vs (validVars . (:vs)) ret }
       d <- promelaEffect k
       modify $ \s -> s { vars = maybe vs (validVars . (:vs)) ret
                        , rec_stack = (xf,f,l,restore $+$ d):rec_stack s
                        }
       return (d_step place)
  where
    args = take (length as - 2) as
    kont = head $ drop (length as - 2) (trace (printf "***kont*** %s" (render $ pretty as)) as)
    -- (Src x _, retVal)   = unwrapRecursiveCont kont
    -- (retX, t, mretDecl) = promelaVal retVal
    (xt, k) = case kont of
                AbsEff (Src x t) k -> (Just (x,t), k)
                k                  -> (Nothing, k)
    -- (AbsEff (Src x t) k)        = case kont of
    --                                 AbsEff (Src x t) k -> kont
    --                                 _ -> tracepp "kont was actually" kont
    ret = do (x,to) <- xt
             ty     <- to
             return x
    restore = maybe empty goRestore ret
    goRestore r
      | symbolString r /= "_"
      = copyVal (promela r) (promela retVar) <> semi
      | otherwise
      = empty
    -- ret = maybe Nothing (\(x,t) -> maybe Nothing (Just . const x) t) xt

stackFrame f = stackName f <> brackets (stackPtrName f <+> text "-" <+> int 1)
oldStackFrame f = stackName f <> brackets (stackPtrName f <+> text "-" <+> int 2)

popActivationRecord f ls forms
  = intType <+> pcRecord <> semi $+$
    (d_step $
       pcRecord <+> equals <+> frame <> text "." <> pcRecord <> semi $+$
       assignLocals $+$
       assignArgs)
  where
    frame      = stackFrame f
    assignArgs = vcat [ copyVal (promela x) (frame `dot` promela x) <> semi
                      | x <- forms
                      ]
    assignLocals = vcat [ copyVal (promela x) (frame `dot` promela x) <> semi
                        | x <- ls
                        ]

assnField f x y = x `dot` f <+> equals <+> y
copyField f x y = assnField f x (y `dot` f)

saveLocals :: Fp.Symbol -> [Fp.Symbol] -> [Fp.Symbol] -> [Effect] -> Int -> Doc
saveLocals f ls forms args pc
  = d_step $
      saveLocals $+$
      saveArgs   $+$
      savePC
  where
    oldName    = oldStackFrame f
    savePC     = oldName <> text "." <> pcRecord <+> equals <+> int pc <> semi
    saveArgs   = vcat [ copyVal (oldName `dot` promela f) (promela f) <> semi
                      | f <- forms
                      ]
    saveLocals = vcat [ copyVal (oldName `dot` promela l) (promela l) <> semi
                      | l <- ls
                      ]

pushArgs :: [Fp.Symbol]
         -> Fp.Symbol
         -> [Fp.Symbol]
         -> [Fp.Symbol]
         -> [Effect]
         -> Int
         -> ([Fp.Symbol], Doc)
pushArgs env f ls forms args pc
  = (vars, push)
  where
    vars       = fst <$> mds
    push       = newPC      $+$
                 argDecls   $+$
                 newArgs
    name       = stackFrame f
    newPC      = name <> text "." <> pcRecord <+> equals <+> int 0 <> semi
    mds        = [ (x,md) | (x,_,md) <- promelaVal env <$> args ]
    argDecls   = vcat . catMaybes $ (snd <$> mds)
    newArgs    = vcat [ copyVal (name `dot` promela f) (promela x) <> semi
                      | (f,x) <- zip forms (fst <$> mds)
                      ]

newLabel :: Fp.Symbol -> PM Int
newLabel f
  = do l <- fromJust . lookup f <$> gets rec_label
       modify $ \s -> s { rec_label = update <$> rec_label s }
       return (l + 1)
  where
    update (f',l') = if f == f' then (f',l'+1) else (f',l')

unwrapRecursiveCont (AbsEff x (AppEff (AppEff _ v) _)) = (x,v)
unwrapRecursiveCont (AbsEff x (AppEff _ v)) = (x,v)
unwrapRecursiveCont e = error (printf "unwrap: %s\n" (render $ pretty e))

promelaVal :: [Fp.Symbol] -> Effect -> (Fp.Symbol, Type, Maybe Doc)
promelaVal env (EffVar (Src x _))
  | x == Fp.symbol (dataConWorkId unitDataCon)
  = (symbol "unit", unitTy, Nothing)
promelaVal env (EffVar (Src x _))
  | symbolString x == (symbolString $ Fp.symbol (dataConWorkId trueDataCon))
  = (symbol "true_val", unitTy, Nothing)
promelaVal env (EffVar (Src x _))
  | symbolString x == (symbolString $ Fp.symbol (dataConWorkId falseDataCon))
  = (symbol "false_val", unitTy, Nothing)
promelaVal env (EffVar (Src x Nothing)) -- Variable lookup
  = (x, error (printf "uh oh needed a type %s" (Fp.symbolString x)), Nothing)
promelaVal env (EffVar (Src x (Just t))) -- Variable lookup
  | x `elem` env
  = (x, t, Nothing)
  | otherwise
  = havoc x t
promelaVal env (Pend (EffVar (Src x (Just t))) info) -- Possibly an expression?
  | Just d <- maybeInfoVal env x info
  = (x, t, Just d)
  | otherwise
  = promelaVal env $ EffVar (Src x (Just t))
promelaVal env (Pend e (Info  x t _ g))
  = promelaVal env (EffVar (Src x (Just t)))
promelaVal env e = error (printf "\n\n*****promelaVal:\n%s\n******\n\n" (render (pretty e)))

havoc x t
  | tyName t == pidType
  = (x, t, Just declX)
  | otherwise
  = (x, t, Nothing)
  where
    declX = ptrType <+> promela x <> semi $+$
            text "select" <> parens (promela x <+> colon <+> int 0 <+> text ".." <+> promela maxProcsVar) <> semi $+$
            promelaMacro "assume" [promela x <+> text "<" <+> promela pidCtrName]

promelaCstrVal :: CstrInfo -> [Fp.Expr] -> Doc
promelaCstrVal c args
  | null (cargs c) = empty
  | otherwise      = hcat (go <$> (zip (zip (cargs c) [1..]) args))
  where
    go ((f, i), Fp.EVar a)
       =  tmpName (promela (cname c)) <> text "." <> argName f i
      <+> equals
      <+> promela a <> semi

tmpName n = n <> text "_tmp"

obj :: Fp.Symbol -> Fp.Symbol -> Doc
obj ty idx
  = heapName ty <> brackets (promela idx `dot` valueField)

access :: Fp.Symbol -> Fp.Symbol -> Fp.Symbol -> Doc
access ty idx fld
  = obj ty idx <> text "." <> promela fld

promelaVar :: Fp.Symbol -> PM Doc
promelaVar x
  | x == Fp.symbol (dataConWorkId unitDataCon)
  = return $ int 1
  | otherwise
  = error "\n\npromelaVar\n\n"

maybeInfoVal :: [Fp.Symbol] -> Fp.Symbol -> Info -> Maybe Doc
maybeInfoVal env x (maybeCstrApp -> Just (cinfo, args))
  = Just $ maybeDecl $+$
           d_step (
             setValidBit x (text "true") <> semi $+$
             promela x `dot` valueField <+> equals <+> heapPtrName tyname <> semi $+$
             heapPtrName tyname <> text "++" <> semi $+$
             access tyname x (symbol "tag") <+> equals <+> int (ctag cinfo) <> semi $+$
             vcat (go <$> (zip [0..] args))
           )
  where
    maybeDecl = if x `elem` env then empty else ptrType <+> promela x <> semi
    go (i,Fp.EVar a)
      = copyVal (obj tyname x <> cstr <> brackets (int i)) (promela a) <> semi $+$ empty
    cstr = text ".c" <> int (ctag cinfo)
    tyname = ctype cinfo
maybeInfoVal env x (maybeInt -> Just i)
  = Just $ defineConcrete env [] x (int i) <> semi
    -- maybeDeclDoc env x (int i) <> semi
maybeInfoVal env x (maybeExpr -> Just (xs, e))
  -- = Just $ maybeDeclDoc env x e <> semi
  = Just $ defineConcrete env xs x e <> semi
maybeInfoVal env x _
  = Nothing

defineConcrete :: [Fp.Symbol] -> [Fp.Symbol] -> Fp.Symbol -> Doc -> Doc
defineConcrete env deps x d
  = decl_x $+$
    d_step (x_valid deps $+$ lval <+> equals <+> rval)
  where
    decl_x
      | x `elem` env
      = empty
      | otherwise
      = ptrType <+> promela x <> semi
    x_valid [] = promela x `dot` validBit <+> equals <+> text "true" <> semi
    x_valid (d:ds)
      = promela x `dot` validBit <+> equals <+>
        foldl go (promela d `dot` validBit) ds <> semi
    go x y = x <+> text "&&" <+> promela y `dot` validBit
    lval = promela x `dot` valueField
    rval = d

dot x y = x <> text "." <> y
validBit   = text "p"
valueField = text "v"
setValidBit x e = promela x `dot` validBit <+> equals <+> e


maybeDeclDoc :: [Fp.Symbol] -> Fp.Symbol -> Doc -> Doc
maybeDeclDoc env x def
  | x `elem` env
  = assgn
  | otherwise
  = ptrType <+> assgn
  where
    assgn = promela x <+> equals <+> def


eqpreds :: Fp.Reft -> [Fp.Expr]
eqpreds (Fp.Reft (vv,e))
  = [ e' | (Fp.PAtom Fp.Eq (Fp.EVar vv) e') <- Fp.conjuncts e ]

propPreds :: Fp.Reft -> [Fp.Expr]
propPreds (Fp.Reft (vv,e))
  = [ e' | (Fp.PIff x e') <- Fp.conjuncts e, x == Fp.eProp vv ]

extractPreds :: (Fp.Expr -> Maybe ([Fp.Symbol], a))
             -> Fp.Reft
             -> [([Fp.Symbol], a)]
extractPreds f e
  = catMaybes (f <$> eqpreds e)

extractPropPreds :: (Fp.Expr -> Maybe a) -> Fp.Reft -> [a]
extractPropPreds f e
  = catMaybes (f <$> propPreds e)

maybeExpr :: Info -> Maybe ([Fp.Symbol], Doc)
maybeExpr (Info x ty reft g)
  = case extractPreds go (R.rTypeReft reft) of
      c:_ -> Just c
      _    -> Nothing
  where
    go (Fp.EBin op e1 e2)
      = do (syms1, d1) <- go e1
           (syms2, d2) <- go e2
           o  <- goOp op
           return $ (nub (syms1 ++ syms2), parens (d1 <+> o <+> d2))
    go (Fp.EVar x)   = Just $ ([x], promela x `dot` valueField)
    go (Fp.ECst e _) = go e
    go (Fp.ECon (Fp.I i)) = Just ([], int (fromInteger i))
    go _ = Nothing
    goOp Fp.Plus  = Just $ text "+"
    goOp Fp.Minus = Just $ text "-"
    goOp _ = Nothing
maybeInt :: Info -> Maybe Int
maybeInt (Info x ty reft g)
  = case extractPreds go (R.rTypeReft reft) of
      (_,c):_ -> Just c
      _   -> Nothing
  where
    go (Fp.ECst e _)      = go e
    go (Fp.ECon (Fp.I i)) = return ([], fromInteger i)
    go _ = Nothing
maybeCstrApp :: Info -> Maybe (CstrInfo, [Fp.Expr])
maybeCstrApp (Info x ty reft g)
  = case extractPreds go (R.rTypeReft reft) of
      c:_ -> Just (snd c)
      _   -> Nothing
  where
    go (Fp.EVar f) =
      case cstrFor f ty of
        Just cinfo -> Just ([], (cinfo, []))
        _          -> Nothing
    go (Fp.splitEApp -> (Fp.EVar f, as)) =
      case cstrFor f ty of
        Just cinfo -> Just ([], (cinfo, as))
        _          -> Nothing
    go _ = Nothing

maybeSend :: Effect -> Maybe (Effect, Effect)
maybeSend (AppEff (AppEff (AppEff (EffVar (Src f _)) _) p) m)
  | symbolString f == "send"
  = Just (p, m)
maybeSend _
  = Nothing

maybeRecv :: Effect -> Maybe Symbol
maybeRecv (AppEff (EffVar (Src f _)) (EffVar (Src me _)))
  | symbolString f == "recv" = Just me
  | otherwise = Nothing
maybeRecv _
  = Nothing

maybeRecursive :: Effect -> Maybe (Symbol, Effect, ([Binder], [Effect]), Effect, Fp.Symbol)
maybeRecursive = go [] [] []
  where
    go fs is as (Mu x (AbsEff f bdy))
      = go (f:fs) is as (Mu x bdy)
    go fs is as (Mu x (Pend e i))
      = go fs (i:is) as (Mu x e)
    go fs is as (Mu x bdy)
      = Just (x, sub [(me, meArg)] infoBody, (reverse fs', as'), kArg, me)
      where
        infoBody = foldl' Pend bdy is
        fs'  = drop 2 fs
        [(Src me _), k] = take 2 (tracepp "fs" fs)
        as'  = take (length as - 2) as
        [kArg, EffVar (Src meArg _)] = drop (length as - 2) as
    go [] is as (AppEff x e)
      = go [] is (e:as) x
    go _ _ _ _
      = Nothing

maybeRecursiveCall :: Effect -> PM (Maybe (Fp.Symbol, Fp.Symbol, [Binder], [Fp.Symbol], [Effect]))
maybeRecursiveCall (breakArgs -> Just (EffVar (Eff x), as))
  = do rs <- gets rec_funs
       return . fmap go $ find p rs
  where
    p  (x',_,_,_) = x == x'
    go (x,f,forms,ls)  = (x,f,forms,ls,as)
maybeRecursiveCall e
  = return Nothing

breakArgs (AppEff m n) = Just $ go [n] m
  where
    go as (AppEff m n)
      = go (n:as) m
    go as e = (e, as)
breakArgs _ = Nothing

isRecv :: Effect -> Bool
isRecv (AppEff (EffVar (Src f _)) _)
  = symbolString f == "recv"
isRecv _
  = False

declareType :: TypeInfo -> Doc
declareType ty@TypeInfo{}
  = text "typedef" <+> name $+$ braces body
  where
    name  = promela (tyname ty)
    body  = vcat ( text "int tag;" : (go <$> cinfo ty) )
    go ci = ptrType <+> text "c" <> int (ctag ci) <> brackets (int (max 1 (length (cargs ci)))) <> semi
argName :: Fp.Symbol -> Int -> Doc
argName s i = text "arg_" <> int i

--------------------------------
-- Extracting/Representing Types
--------------------------------
instance Promela Type where
  promela ty = promela (tyName ty) <> text "_ty"

data TypeInfo = TypeInfo { tyname :: Fp.Symbol
                         , cinfo  :: [CstrInfo]
                         }
              | PrimType { tyname :: Fp.Symbol }
 deriving (Eq, Show)


data CstrInfo = CstrInfo {
    ctype :: Fp.Symbol
  , ctag  :: Int
  , cname :: Fp.Symbol
  , cargs :: [Fp.Symbol] -- the types of the arguments
  } deriving (Eq, Show)

type PrimTy = Type
type ADT    = Type
type Arg    = Type

cstrFor :: Fp.Symbol -> Type -> Maybe CstrInfo
cstrFor f (tyInfo -> tinfo@TypeInfo{})
  = case [ ci | ci <- cinfo tinfo, symbolString (cname ci) == symbolString f ] of
      [ci] -> Just ci
      []   -> Nothing
cstrFor _ _
  = Nothing

primTyInfo :: (TyCon, [Arg]) -> TypeInfo
primTyInfo (ty, _)
  = adtTyInfo (ty,[])

pidType :: Symbol
pidType = symbol "Control.Process.MessagePassing.Pid"

adtTyInfo :: (TyCon, [Arg]) -> TypeInfo
adtTyInfo (ty, _)
  | getUnique ty == boolTyConKey
  = PrimType { tyname = symbol ty }
  | getUnique ty == intTyConKey
  = PrimType { tyname = symbol ty }
  | ty == unitTyCon
  = PrimType { tyname = symbol ty }
  | name == pidType
  = PrimType { tyname = symbol ty }
  | otherwise
  = TypeInfo { tyname = name
             , cinfo  = adtCInfo ty name
             }
  where
    name = symbol $ getName ty

tyName :: Type -> Fp.Symbol
tyName (tyConAppTyCon_maybe -> Just tc)
  = Fp.symbol . getName $ tc
tyName x
  | Just v <- getTyVar_maybe x
  = Fp.symbol . getName $ v
tyName x
  = error "bloop"
adtCInfo :: TyCon -> Fp.Symbol -> [CstrInfo]
adtCInfo tc tn
  = go <$> tyConDataCons tc
  where
    go dc = CstrInfo {
              ctype = tn
            , ctag  = dataConTag dc
            , cname = Fp.symbol $ dataConWorkId dc
            , cargs = tyName <$> dataConOrigArgTys dc
            }


partitionTypes :: [Type] -> ([(TyCon, [Arg])], [(TyCon, [Arg])])
partitionTypes tys
  = (prims, adts)
  where
    prims  = filter (isPrimTyCon . fst) tcapps
    adts   = filter (isAlgTyCon . fst) tcapps
    tcapps = mapMaybe splitTyConApp_maybe tys

tyInfo :: Type -> TypeInfo
tyInfo t = head $ tyInfos [t] -- wow this is stupid..

tyInfos :: [Type] -> [TypeInfo]
tyInfos tys
  = (primTyInfo <$> prims) ++ (adtTyInfo <$> adts)
  where
    (prims, adts) = partitionTypes tys

tyBoundTys :: EffTy -> [(Symbol, Type)]
tyBoundTys t = concatMap boundTys (effs t)

tySends :: EffTy -> [Info]
tySends t = concatMap sends (effs t)

effs t = everything (++) (mkQ [] go) t
  where
    go :: EffTy -> [Effect]
    go (EffTerm e) = [e]
    go _           = []

sends :: Effect -> [Info]
sends e = everything (++) (mkQ [] go) e
  where
    go :: Effect -> [Info]
    go (AppEff (AppEff (EffVar (Src s (Just _))) _) (Pend _ x))
      | symbolString s == "send" =  [x]
    go _ = []

boundTys :: Effect -> [(Symbol, Type)]
boundTys e = everything (++) (mkQ [] go) e
  where
    go (Src b (Just t)) = [(b,t)]
    go _                = []
