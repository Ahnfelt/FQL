import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad.State.Strict as StateM
import Control.Monad.State.Strict (get, put, runState)

type State a = StateM.State Work a

data E = EN Int | EB Bool | EVar Var | EPlus E E
       | EEqual E E | EIf E E E | EPair E E | ELambda P E 
       | EApp E E | ELet Var E E | ERec Var E 
       | ESet [E] | EUnion E E
         deriving (Show, Eq)

data P = PVar Var | PPair P P 
         deriving (Show, Eq)

data T = TInt | TBool | TFun T T | TPair T T | TSet T | TVar Var
         deriving (Eq, Ord)

instance Show T where
    show (TInt) = "int"
    show (TBool) = "bool"
    show (TFun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show (TPair t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
    show (TSet t) = "{"++ show t ++ "}"
    show (TVar v) = show v

data Var = VNumber Int | VName String deriving (Eq, Ord)

instance Show Var where
    show (VNumber n) = "t"++show n
    show (VName n) = n

data Constraint = Constraint T T deriving Eq

instance Show Constraint where
    show (Constraint t1 t2) = show t1 ++ " = " ++ show t2

data Work = Work [Constraint] (Map.Map Var T) (Set.Set T) Int

instance Show Work where
    show (Work l m _ _) = 
              drop 1 (foldl (\x y -> x ++ "\n" ++ show y) 
                    "" l ++ "\n") 
           ++ drop 1 (foldl (\x (k, v) -> 
                         x ++ "\n" ++ show k ++ ": " ++ show v)
                  "" (Map.toList m))
  
replace :: Map.Map Var T -> T -> T
replace m (TInt) = TInt
replace m (TBool) = TBool
replace m (TFun t1 t2) = TFun (replace m t1) (replace m t2)
replace m (TPair t1 t2) = TPair (replace m t1) (replace m t2)
replace m (TSet t) = TSet (replace m t)
replace m (TVar v) = case Map.lookup v m of
                       Just t -> replace m t
                       Nothing -> TVar v

rewrite t = do
    (Work _ m _ _) <- get
    return $ replace m t

newVar = do 
  (Work l m q i) <- get
  put $ Work l m q (i+1)
  return $ TVar $ VNumber i

constraint :: T -> T -> State ()
constraint t1 t2 = do 
  (Work l m q i) <- get 
  put $ Work (Constraint t1 t2 : l) m q i

equality :: T -> State ()
equality t = do
  (Work l m q i) <- get 
  put $ Work l m (Set.insert t q) i

bind v t = do
    Work l m q i <- get
    put $ Work l (Map.insert v t m) q i

free t = do
    t' <- rewrite t
    return $ free' t'
    where
        free' (TVar v) = Set.singleton v
        free' (TSet t) = free' t
        free' (TPair t1 t2) = free' t1 `Set.union` free' t2
        free' (TFun t1 t2) = free' t1 `Set.union` free' t2
        free' (TInt) = Set.empty
        free' (TBool) = Set.empty

freeEnv e = do
    l <- mapM f (Map.elems e)
    return $ Set.unions l
    where
        f (_, t) = do
            t' <- rewrite t
            free t'

occurs v t = do
    f <- free t
    return $ Set.member v f

isEquality (TVar v') = True
isEquality (TSet t) = isEquality t
isEquality (TPair t1 t2) = isEquality t1 && isEquality t2
isEquality (TFun t1 t2) = False
isEquality (TInt) = True
isEquality (TBool) = True

allEquality (Work _ m q _) =
    all m (Set.toList q)
    where
        all m [] = Nothing
        all m (t:ts) = let t' = replace m t in
            if isEquality t' 
                then all m ts
                else Just (show t' ++ " is not an equality type")

problem t1 t2 a = do
    t1' <- rewrite t1
    t2' <- rewrite t2
    return $ Just
               ("Cannot unify " ++ show t1' ++ " with " ++ show t2'
                                    ++ " " ++ a)

unify :: T -> T -> State (Maybe String)
unify (TVar v) t = do
    t' <- rewrite (TVar v)
    t'' <- rewrite t
    case t' of
        TVar v' -> case t'' of
            TVar v'' | v' == v'' -> return Nothing
            _ -> do
                o <- occurs v' t''
                if o
                    then problem t' t'' "(occurs check)"
                    else do
                        bind v' t''
                        return Nothing
        _ -> do 
            constraint t' t''
            return Nothing
unify t (TVar v) = unify (TVar v) t
unify (TSet t1) (TSet t2) = unify t1 t2
unify (TPair t1 t2) (TPair t3 t4) = do
  constraint t1 t3
  constraint t2 t4
  return Nothing
unify (TFun t1 t2) (TFun t3 t4) = do
  constraint t1 t3
  constraint t2 t4
  return Nothing
unify (TInt) (TInt) = return Nothing
unify (TBool) (TBool) = return Nothing
unify t1 t2 = problem t1 t2 ""

pattern :: P -> State (T, Map.Map Var ([Var], T))
pattern (PVar v) = do 
  t <- newVar
  return (t, Map.singleton v ([], t))
pattern (PPair p1 p2) = do
  (t1, m1) <- pattern p1
  (t2, m2) <- pattern p2
  return (TPair t1 t2, Map.union m2 m1)
-- TODO: Check duplicate vars

infer :: Map.Map Var ([Var], T) -> E -> T -> State ()
infer env (EN _) t         = constraint t TInt 
infer env (EB _) t         = constraint t TBool
infer env (EPlus e1 e2) t  = do 
  v1 <- newVar
  v2 <- newVar
  constraint v1 TInt
  constraint v2 TInt
  constraint t TInt
  infer env e1 v1
  infer env e2 v2
infer env (EEqual e1 e2) t = do 
  v1 <- newVar
  v2 <- newVar
  constraint v1 v2
  constraint t TBool
  equality v1
  infer env e1 v1
  infer env e2 v2
infer env (EIf e1 e2 e3) t = do 
  v1 <- newVar
  v2 <- newVar
  v3 <- newVar
  constraint v1 TBool
  constraint v2 v3
  constraint t v2
  infer env e1 v1
  infer env e2 v2
  infer env e3 v3
infer env (EPair e1 e2) t  = do 
  v1 <- newVar 
  v2 <- newVar
  constraint t $ TPair v1 v2
  infer env e1 v1
  infer env e2 v2
infer env (EVar v) t       = 
    case Map.lookup v env of
        Just (l, t') -> do
            l' <- mapM (\v' -> do 
                v'' <- newVar
                return (v', v'')) l
            let t'' = replace (Map.fromList l') t'
            constraint t t''
infer env (ELet v e1 e2) t = do
  v1 <- newVar
  v2 <- newVar
  infer env e1 v1
  s <- solve
  case s of
    Just v -> error v
    Nothing -> return ()
  constraint t v2
  v1' <- rewrite v1
  f <- free v1'
  f' <- freeEnv env
  let l = Set.toList (f Set.\\ f')
  let env' = Map.insert v (l, v1') env
  infer env' e2 v2
infer env (ELambda p e) t  = do
  (t', env') <- pattern p
  let env'' = Map.union env' env
  v1 <- newVar
  constraint t $ TFun t' v1
  infer env'' e v1 
infer env (EApp e1 e2) t   = do 
  v1 <- newVar 
  v2 <- newVar
  constraint v1 $ TFun v2 t
  infer env e1 v1
  infer env e2 v2
infer env (ERec v e) t     = do 
  v1 <- newVar 
  v2 <- newVar
  constraint v1 v2
  constraint v1 t
  let env' = Map.insert v ([], v1) env 
  infer env' e v2
infer env (ESet es) t      = do 
  v1 <- newVar 
  constraint t $ TSet v1
  equality v1
  mapM (\e -> infer env e v1) es
  return ()
infer env (EUnion e1 e2) t = do 
  v1 <- newVar 
  v2 <- newVar
  v3 <- newVar 
  infer env e1 v1
  infer env e2 v2
  constraint t v1
  constraint t v2
  constraint t $ TSet v3

solve :: State (Maybe String)
solve = do
  Work l m q i <- get
  case l of 
    [] -> do
        w <- get
        return $ allEquality w
    Constraint c1 c2 : cs -> do
           put $ Work cs m q i
           e <- unify c1 c2
           case e of
             Just v -> return $ Just v
             Nothing -> solve

---------------------------------------------------------------------
main = do
    let ((), w) = runState 
            (infer Map.empty chosen (TVar result)) 
            (Work [] Map.empty Set.empty 1)
    putStrLn "----------------------------------------"
    putStrLn "Inferred constraints:"
    print w
    loop w 1
    where
        loop (Work [] m q i) _ = 
            case allEquality (Work [] m q i) of
                Just v -> putStrLn ("\nError: " ++ v)
                Nothing -> do
                    let t = replace m (m Map.! result)
                    putStrLn ("\nSuccess: " ++ show t)
        loop (Work (Constraint t1 t2 : l) m q i) n = do
            let w = Work l m q i
            let (e, w') = runState (unify t1 t2) w
            case e of
                Just v -> putStrLn ("\nError: " ++ v)
                Nothing -> do
                    putStrLn ("\nStep #" ++ show n ++ ":")
                    print w'
                    loop w' (n + 1)
        
        result = VName "res"
        
        chosen = t15 where
            t1 = ELambda (PVar $ VName "a") (EPair (EN 1) (EB True))
            t2 = ELambda (PVar $ VName "a") (EPlus (EN 1) (EB True))
            t3 = EEqual (EPair (EN 7) (EN 8)) (EPair (EN 7) (EN 8))
            t4 = EEqual t1 t1
            t5 = (ELambda (PPair (PVar $ VName "x") (PVar $ VName "y")) 
                (EEqual (EVar $ VName "y") (EVar $ VName "x")))
            t6 = (EPair (EN 5) (EB True))
            t7 = EApp t5 t6
            t8 = EPair (ELambda (PVar $ VName "x") (EN 1)) (EB False)
            t9 = ESet [t8]
            t10 = ESet [EN 7, EN 8]
            t11 = EEqual t8 t8
            t12 = EEqual (EN 7) (EN 8)
            t13 = ELambda (PVar $ VName "z") (EVar $ VName "z")
            t14 = el "f" t13 (EPair 
                (EApp (ev "f") (EN 7)) 
                (EApp (ev "f") (EB True)))
            t15 = el "g" (ef "z" (EPlus (ev "z") (ev "z"))) t14
            
            ev n = EVar $ VName n
            el n e1 e2 = ELet (VName n) e1 e2
            ef n e = ELambda (PVar $ VName n) e
            
