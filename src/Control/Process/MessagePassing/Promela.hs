{-# Language ViewPatterns #-}
module Control.Process.MessagePassing.Promela where

import           Debug.Trace
import           Type
import           Name
import           TyCon
import           DataCon
import           Unique
import           PrelNames
import           Control.Monad.State
import           Text.Printf
import           Data.List
import           Data.Maybe
import           Data.Generics hiding (TyCon, empty)
import           Data.Function
import qualified Language.Fixpoint.Types as Fp
import           Text.PrettyPrint.HughesPJ hiding ((<$>))

import           Control.Process.MessagePassing.EffectTypes
import           Control.Process.MessagePassing.PrettyPrint

debug :: Show a => String -> a -> a
debug msg x = trace (msg ++ ": " ++ show x) x

debugEff :: String -> Effect -> Effect
debugEff msg x = trace (msg ++ ": " ++ render (pretty x)) x

class Promela a where
  promela :: a -> Doc

instance Promela EffTy where
  promela (EffTerm e)
    = promelaProgram 5 closed
    where
      closed =
        debugEff "closed"  $
        betaReduce
          (AppEff (AppEff e doneEff) (EffVar (Src (symbol "_init") Nothing)))
      doneEff = AbsEff (Src (symbol "_") Nothing) (AppEff (EffVar (Src (symbol "done") Nothing)) (EffVar (Src (symbol "_init") Nothing)))
  promela _
    = error "I only know how to convert values of type { λK.λme.x }!"

sendProc :: Doc
sendProc =
  text "proctype send(int who; mtype ty; byte msg)" $+$
  text "{" $+$
    nest 2 (text "mbuf[who]!ty,msg") $+$
  text "}"

initialPid :: Symbol
initialPid = symbol "_init"
pidCtrName = symbol "_pidCtr"

retChan :: Symbol
retChan  = symbol "_ret"

callerChan :: Symbol
callerChan  = symbol "_caller"

procName :: Symbol -> Doc
procName s = promela s <> text "proc"

promelaProgram :: Int -> Effect -> Doc
promelaProgram n eff
  = mtype               $+$
    types               $+$
    heaps               $+$
    buf                 $+$
    pidCtr              $+$
    sendProc            $+$
    children            $+$
    functions           $+$
    initialProc master
  where
    (master, st)
      = runState (promelaEffect eff) emptyPState
    children
      = promelaProcs st
    functions
      = promelaFunctions st

    mtype  = declMtype tinfos
    types  = vcat $ declareType <$> tinfos
    cinfos = concatMap cinfo tinfos
    tinfos = nub [t | t@TypeInfo {} <- tyInfos (snd <$> boundTys eff)]
    heaps  = vcat $ goHeap  <$> tinfos
    goHeap ti = heapDecl 10 (tyname ti)
    pidCtr = ptrType <+> promela pidCtrName
         <+> equals <+> int 1 <> semi

    -- N channels --
    numChans = n
    buf      = chanDecl n n

promelaProcs :: PState -> Doc
promelaProcs st
  = vcat (go <$> procs st)
  where
    go (name, args, body)
      = text "proctype" <+> procName name <+> formalsList args <+> text "{" $+$
        nest 2 body $+$
        text "}"

promelaFunctions :: PState -> Doc
promelaFunctions st
  = vcat (go <$> recs st)
  where
    template f args body
      = text "proctype" <+> promela f <+>
        funFormalsList (callerChan:args) <+> text "{" $+$
        nest 2 body $+$
        text "}"
    go (x,f,as,vs,Just bdy)
      = template f (as ++ vs) bdy --empty -- undefined -- promelaRecursiveDef x f bdy

initialProc d =
  text "active proctype master() {" $+$
  nest 2 (text "int" <+> promela initialPid <+> text " = 0;" $+$ d) $+$
  text "}"

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
ptrType = text "byte"

objIdType :: Doc
objIdType = text "byte"

tableDecl :: Int -> TypeInfo -> Doc
tableDecl n ti
  = ptrType <+> tableName ti <> brackets (int n) <> semi

heapDecl :: Int -> Fp.Symbol -> Doc
heapDecl n ti
  = promela ti <+> heapName ti <> brackets (int n) <> semi $+$
    ptrType <+> heapPtrName ti <+> equals <+> int 0 <> semi

tableName :: TypeInfo -> Doc
tableName ti = promela (tyname ti) <> text "_table"

heapName :: Fp.Symbol -> Doc
heapName ty = promela ty <> text "_heap"

heapPtrName :: Fp.Symbol -> Doc
heapPtrName ty = promela ty <> text "_heap_ptr"

data SrcPattern = InitDecl Fp.Symbol (Maybe Type) Doc
                | Send Effect Effect

instance Promela Fp.Symbol where
  promela s = text (cleanup <$> symbolString s)
    where
      cleanup = replace '.' '_'
              . replace '#' '_'
              . replace '$' '_'
              . replace '\'' '_'
              . replace '(' 't'
              . replace ')' 't'
      replace x y c = if c == x then y else c

data PState = PState {
    vars  :: [Fp.Symbol]
  , procs :: [(Fp.Symbol, [Fp.Symbol], Doc)]
  , recs  :: [(Fp.Symbol, Fp.Symbol, [Fp.Symbol], [Fp.Symbol], Maybe Doc)] -- variable, procname, args, body
  , n     :: Int
  }
type PM a = State PState a

emptyPState :: PState
emptyPState = PState { vars = [initialPid], procs = [], n = 0, recs = [] }

atomic :: Doc -> Doc
atomic d
  = text "atomic" <+> braces d

incPidCtr = promela pidCtrName <> text "++" <> semi

promelaEffect :: Effect -> PM Doc
promelaEffect e = do recCall <- maybeRecursiveCall e
                     go recCall e
  where
    go (Just (f, as, vs)) _
      = promelaRecursiveCall f as vs
    go _ (maybeSend -> Just (p,m))
      = promelaSend p m
    go _ (maybeRecursive -> Just (x, bdy, (fs,as), k, me))
      = promelaRecursive x bdy (fs,as) k me
    go _ (Nu x (Par e1 e2))
      = promelaNu x e1 e2
    go _ (Bind m (AbsEff (Src x t) n))
      = promelaBind m (x,t) n
    go _ (NonDet es)
      = promelaNonDet es
    go _ (Assume i unfolds e)
      = promelaAssume i unfolds e
    go _ (AppEff (EffVar (Src f _)) _)
      | symbolString f == "done"
      = return $ text "true"
      | symbolString f == "die"
      = return $ text "assert (0 == 1)"
    go _ (EffVar (Src f _))
      = return $ promela f
    go _ (AppEff (EffVar (Eff f)) e)
      = return $ maybe ret (\d -> d $+$ ret) d
      where
        ret = promela callerChan <> text "!!" <> promela x
        (x, _, d) = promelaVal e
    go _ e = error (render $ text "promelaEffect:" <+> pretty e)

argList :: [Fp.Symbol] -> Doc
argList = parens . hcat . punctuate comma . fmap promela

formalsList :: [Fp.Symbol] -> Doc
formalsList = parens . hcat . punctuate semi . fmap go
  where
    go s = ptrType <+> promela s

funFormalsList :: [Fp.Symbol] -> Doc
funFormalsList (c:cs)
  = parens . hcat . punctuate semi $ chan : (go <$> cs)
  where
    chan = text "chan" <+> promela callerChan
    go s = ptrType <+> promela s

promelaNonDet es
  = do ds <- mapM go es
       return $
         text "if" $+$
              nest 2 (vcat ds) $+$
         text "fi"
  where
    go e = do vs <- gets vars
              d <- promelaEffect e
              modify $ \s -> s { vars = vs }
              return (text "::" <+> d)

promelaAssume i@(Info (x,ty,reft)) (c,ys) e
  | PrimType {tyname = t} <- tyInfo ty,
    (Just d) <- maybeCompare i
  = do e' <- promelaEffect e
       let x = if getUnique c == trueDataConKey
               then d else text "!" <> parens d
       return $ x <+> text "->" <+> braces e'
promelaAssume (Info (x,ty,reft)) (c,ys) e
  = do modify $ \s -> s { vars = ys ++ vars s }
       d <- promelaEffect e
       return $ assm $+$ nest 2 (braces (decls $+$ d))
  where
    dcname      = symbol (dataConWorkId c)
    tag         = int . ctag $ fromMaybe err (cstrFor dcname ty)
    err         = error $ (printf "*****\nCan't find info for %s\n*****" (symbolString dcname))
    decls       = vcat (decl <$> (zip [0..] ys))
    assm        = obj t x <> text ".tag" <+> equals <> equals <+> tag <+> text "->"
    decl (i, y) = ptrType <+> promela y <+>
                  equals <+>
                  obj t x <> (text ".c" <> tag <> brackets (int i)) <> semi
    t           = tyname (tyInfo ty)

maybeCompare :: Info -> Maybe Doc
maybeCompare (Info (x,ty,reft@(Fp.RR _ (Fp.Reft(vv,_)))))
  = case extractPropPreds go reft of
      c:_ -> Just c
      _   -> Nothing
  where
    go (Fp.PAtom o e1 e2) = do e1' <- go e1
                               e2' <- go e2
                               o'  <- goOp o
                               return $ parens (e1' <+> o' <+> e2')
    go (Fp.EVar x)        = Just $ promela x
    go (Fp.ECon (Fp.I i)) = Just $ int (fromInteger i)
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
       let args = c : vs
       modify $ \s -> s { vars = args }
       p <- promelaEffect e1
       modify $ \s -> s { vars = args }
       d <- promelaEffect e2
       modify $ \s -> s { vars = args
                        , procs = (c, args, p) : procs s
                        }
       return $
         objIdType <+> promela c <+> equals <+> promela pidCtrName <> semi $+$
         incPidCtr $+$
         text "run" <+> procName c <> argList args <> semi $+$
         d

promelaBind :: Effect -> (Fp.Symbol, Maybe Type) -> Effect -> PM Doc
promelaBind e1 (x,t) e2
  | Just (p,m) <- maybeSend e1
  = do d1 <- promelaSend p m
       d2 <- promelaEffect e2
       return $ (d1 <> semi $+$ d2)
  | Just p <- maybeRecv e1
    = promelaRecv p (x,t) e2
  | otherwise
  = error (printf "promelaBind: %s" (render $ pretty (Bind e1 (AbsEff (Src x t) e2))))

promelaRVal :: Effect -> Doc
promelaRVal e
  = error (printf "rval: %s" (render $ pretty e))

promelaSpawn p args
  = text "run" <+> p <> parens (hcat $ punctuate comma args)

promelaRecv p (x, Just t) e2
  = do d <- promelaEffect e2
       return (decl <> semi $+$ recv <> semi $+$ d)
  where
    decl = if symbolString x == "_" then empty else ptrType <+> promela x
    recv = text "mbuf" <> brackets (promela p) <>
           text "??" <> ty <> comma <> promela x
    ty   = promela t

promelaSend :: Effect -> Effect -> PM Doc
promelaSend p m
  =  return $ (maybe empty (\d -> (d $+$ empty )) decls)
           <> (maybe spawn (\d -> (d $+$ spawn)) decls')
  where
    spawn = promelaSpawn (text "send")
              [promela xP, promela ty, promela xM]
    (xP, _,  decls)  = promelaVal p
    (xM, ty, decls') = promelaVal m

promelaRecursive x bdy (fs,as) (AbsEff ret@(Src r (Just t)) k) me
  = do vs    <- gets vars
       -- The arguments to the recursive function should be
       -- the ret channel + args + in-scope vars at the first call
       let (xs,mds) = unzip [ (x,d) | (x,_,d) <- promelaVal <$> as ]
           ds = catMaybes mds
           decls = if null ds then empty else vcat ((<> semi) <$> ds)
       rdef@(_,f,_) <- promelaRecursiveDef x bdy (symbol <$> fs) vs
       modify $ \s -> s { vars = r:vs }
       let call = text "run" <+> promela f <> argList (retChan : xs ++ vs ) <> semi
       d        <- promelaEffect k
       let wait = promela retChan <> text "??" <> promela r <> semi
           decl = ptrType <+> promela r <> semi
       return $ decls $+$ call $+$ decl $+$ wait $+$ d

promelaRecursiveDef x bdy xs vs
  = do i     <- gets n
       recs  <- gets recs
       let f = symbol ("rec_fun_" ++ show i)
       modify $ \s -> s { n    = i + 1
                        , recs = (x,f,xs,vs,Nothing):recs
                        }
       bdy'   <- promelaEffect (dropArgs bdy)
       modify $ \s -> s { recs = (x,f,xs,vs,Just bdy'):recs, vars = vs }
       return (x,f,Just bdy')
  where
    dropArgs (AbsEff _ e) = dropArgs e
    dropArgs e            = e

promelaRecursiveCall :: Fp.Symbol -> [Effect] -> [Fp.Symbol] -> PM Doc
promelaRecursiveCall f as vs
  = do let (xs, mds) = unzip [(x,d) | (x,_,d) <- promelaVal <$> args ]
           call     = text "run" <+> promela f <+> argList (retChan : xs ++ vs) <> semi
           wait     = ptrType <+> promela x <> semi $+$
                      promela retChan <> text "??" <> promela x <> semi
           retCall  = promela callerChan <> text "!!" <> promela retX
           decls    = vcat $ catMaybes mds
           returns  = maybe retCall (\d -> d $+$ retCall) mretDecl
       return (decls $+$ call $+$ wait $+$ returns)
  where
    args = take (length as - 2) as
    kont = head $ drop (length as - 2) (trace (printf "***kont*** %s" (render $ pretty as)) as)
    (Src x _,retVal)    = unwrapRecursiveCont kont
    (retX, t, mretDecl) = promelaVal retVal

unwrapRecursiveCont (AbsEff x (AppEff (AppEff _ v) _)) = (x,v)
unwrapRecursiveCont (AbsEff x (AppEff _ v)) = (x,v)
unwrapRecursiveCont e = error (printf "unwrap: %s\n" (render $ pretty e))

promelaVal :: Effect -> (Fp.Symbol, Type, Maybe Doc)
promelaVal (EffVar (Src x Nothing)) -- Variable lookup
  = (x, error (printf "uh oh needed a type %s" (Fp.symbolString x)), Nothing)
promelaVal (EffVar (Src x (Just t))) -- Variable lookup
  = (x, t, Nothing)
promelaVal (Pend (EffVar (Src x (Just t))) info) -- Possibly an expression?
  | Just d <- maybeInfoVal x info = (x, t, Just d)
  | otherwise                     = promelaVal (EffVar (Src x (Just t)))
promelaVal (Pend _ (Info (x,t,_)))
  = (x, t, Nothing)
promelaVal e = error (printf "\n\n*****promelaVal:\n%s\n******\n\n" (render (pretty e)))

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
  = heapName ty <> brackets (promela idx)

access :: Fp.Symbol -> Fp.Symbol -> Fp.Symbol -> Doc
access ty idx fld
  = obj ty idx <> text "." <> promela fld

maybeInfoVal :: Fp.Symbol -> Info -> Maybe Doc
maybeInfoVal x (maybeCstrApp -> Just (cinfo, args))
  = Just $ (ptrType <+> promela x <+> equals <+> heapPtrName tyname <> semi) $+$
           (heapPtrName tyname <> text "++" <> semi) $+$
           (access tyname x (symbol "tag") <+> equals <+> int (ctag cinfo) <> semi) $+$
           (hcat (go <$> (zip [0..] args)))
  where
    go (i,Fp.EVar a) = obj tyname x <> cstr <> brackets (int i)
                       <+> equals <+> promela a <> semi $+$ empty
    cstr = text ".c" <> int (ctag cinfo)
    tyname = ctype cinfo
maybeInfoVal x (maybeInt -> Just i)
  = Just $ (text "int" <+> promela x <+> equals <+> int i <> semi)
maybeInfoVal x (maybeExpr -> Just e)
  = Just $ (text "int" <+> promela x <+> equals <+> e <> semi)
maybeInfoVal x _
  = Nothing

eqpreds :: Fp.SortedReft -> [Fp.Expr]
eqpreds (Fp.RR _ (Fp.Reft (vv,e)))
  = [ e' | (Fp.PAtom Fp.Eq (Fp.EVar vv) e') <- Fp.conjuncts e ]

propPreds :: Fp.SortedReft -> [Fp.Expr]
propPreds (Fp.RR _ (Fp.Reft (vv,e)))
  = [ e' | (Fp.PIff x e') <- Fp.conjuncts e, x == Fp.eProp vv ]

extractPreds :: (Fp.Expr -> Maybe a) -> Fp.SortedReft -> [a]
extractPreds f e
  = catMaybes (f <$> eqpreds e)
extractPropPreds f e
  = catMaybes (f <$> propPreds e)

maybeExpr :: Info -> Maybe Doc
maybeExpr (Info (x,ty,reft))
  = case extractPreds go reft of
      c:_ -> Just c
      _    -> Nothing
  where
    go (Fp.EBin op e1 e2)
      = do d1 <- go e1
           d2 <- go e2
           o  <- goOp op
           return $ parens (d1 <+> o <+> d2)
    go (Fp.EVar x)   = Just $ promela x
    go (Fp.ECst e _) = go e
    go (Fp.ECon (Fp.I i)) = Just (int (fromInteger i))
    go _ = Nothing
    goOp Fp.Plus  = Just $ text "+"
    goOp Fp.Minus = Just $ text "-"
    goOp _ = Nothing
maybeInt :: Info -> Maybe Int
maybeInt (Info (x,ty,reft))
  = case extractPreds go reft of
      c:_ -> Just c
      _   -> Nothing
  where
    go (Fp.ECst e _)      = go e
    go (Fp.ECon (Fp.I i)) = return (fromInteger i)
    go _ = Nothing
maybeCstrApp :: Info -> Maybe (CstrInfo, [Fp.Expr])
maybeCstrApp (Info (x,ty, reft))
  = case extractPreds go reft of
      [c] -> Just c
      _   -> Nothing
  where
    go (Fp.splitEApp -> (Fp.EVar f, as)) =
      case cstrFor f ty of
        Just cinfo -> Just (cinfo, as)
        _          -> Nothing
    go _ = Nothing

maybeSend :: Effect -> Maybe (Effect, Effect)
maybeSend (AppEff (AppEff (AppEff (EffVar (Src f _)) _) e2) e3)
  | symbolString f == "send"
  = Just (e2, e3)
maybeSend _
  = Nothing

maybeRecv :: Effect -> Maybe Symbol
maybeRecv (AppEff (EffVar (Src f _)) (EffVar (Src me _)))
  | symbolString f == "recv" = Just me
  | otherwise = Nothing

maybeRecursive :: Effect -> Maybe (Symbol, Effect, ([Binder], [Effect]), Effect, Fp.Symbol)
maybeRecursive = go [] []
  where
    go fs as (Mu x (AbsEff f bdy))
      = go (f:fs) as (Mu x bdy)
    go fs as (Mu x bdy)
      = Just (x, bdy, (fs', as'), kArg, me)
      where
        fs'  = drop 2 fs
        [(Src me _), k] = take 2 fs
        as'  = take (length as - 2) as
        [kArg, EffVar (Src meArg _)] = drop (length as - 2) as
    go [] as (AppEff x e)
      = go [] (e:as) x
    go _ _ _
      = Nothing

maybeRecursiveCall :: Effect -> PM (Maybe (Fp.Symbol, [Effect], [Fp.Symbol]))
maybeRecursiveCall (breakArgs -> Just (EffVar (Eff x), as))
  = do rs <- gets recs
       return . fmap go $ find p rs
  where
    p (x',f,forms,vs,bdy) = x == x'
    go (_,f,forms,vs,_) = (f,as,vs)
maybeRecursiveCall _
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
    go ci = objIdType <+> text "c" <> int (ctag ci) <> brackets (int (max 1 (length (cargs ci)))) <> semi
argName :: Fp.Symbol -> Int -> Doc
argName s i = text "arg_" <> int i

--------------------------------
-- Extracting/Representing Processes
--------------------------------
-- data Process = Process {
--     procName :: Fp.Symbol
--   , procEff  :: Effect
--   }

-- splitProcesses :: Effect -> [Process]
-- splitProcesses e = let (master, ps) = go e
--                        init = Process {
--                                 procName = symbol "init"
--                               , procEff  = master
--                               }
--                    in init : ps
--   where
--     go (Nu s (Par e1 e2)) = (e2', Process { procName = s, procEff = e1 } : ps)
--       where
--         (e2', ps) = go e2
--     go (Bind e1 e2)       = (Bind e1' e2', ps ++ qs)
--       where
--         (e1', ps) = go e1
--         (e2', qs) = go e2
--     go e                  = (e, [])

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
  = case [ ci | ci <- cinfo tinfo, cname ci == f ] of
      [ci] -> Just ci
      []   -> Nothing
cstrFor _ _
  = Nothing

primTyInfo :: (TyCon, [Arg]) -> TypeInfo
primTyInfo (ty, _)
  = adtTyInfo (ty,[])

adtTyInfo :: (TyCon, [Arg]) -> TypeInfo
adtTyInfo (ty, _)
  | getUnique ty == boolTyConKey
  = PrimType { tyname = symbol "bool" }
  | getUnique ty == intTyConKey
  = PrimType { tyname = symbol "int" }
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
