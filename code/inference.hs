import qualified Data.Map as Map
import qualified Control.Monad.State.Strict as StateM
import Control.Monad.State.Strict (get, put, runState)

type State a = StateM.State Work a

data E = EN Int | EB Bool | EVar Var | EPlus E E
       | EEqual E E | EIf E E E | EPair E E | ELambda P E 
       | EApp E E | ELet Var E E | ERec Var E 
       | ESet [E] | EUnion E E
         deriving (Show, Eq)

data P = PVar String | PPair P P 
         deriving (Show, Eq)

data T = TInt | TBool | TFun T T | TPair T T | TSet T | TVar Var
         deriving Eq

instance Show T where
    show (TInt) = "int"
    show (TBool) = "bool"
    show (TFun t1 t2) = show t1 ++ "->" ++ show t2
    show (TPair t1 t2) = show t1 ++ " x " ++ show t2 
    show (TSet t) = "{"++ show t ++ "}"
    show (TVar v) = show v

data Var = VNumber Int | VName String deriving (Eq, Ord)

instance Show Var where
    show (VNumber n) = "X_"++show n
    show (VName n) = n

data Constraint = Constraint T T deriving Eq

instance Show Constraint where
    show (Constraint t1 t2) = show t1 ++ " = " ++ show t2

data Work = Work [Constraint] (Map.Map Var T) Int

instance Show Work where
    show (Work l m _) = 
              drop 1 (foldl (\x y -> x ++ "\n" ++ show y) 
                    "" l ++ "\n") 
           ++ drop 1 (foldl (\x (k, v) -> 
                         x ++ "\n" ++ show k ++ " -> " ++ show v)
                  "" (Map.toList m))
    
-- TODO: Make it work on all types
rewrite :: T -> State T
rewrite (TInt) = return TInt
rewrite (TBool) = return TBool
rewrite (TFun t1 t2) = do
  t1' <- rewrite t1
  t2' <- rewrite t2
  return $ TFun t1' t2'
rewrite (TPair t1 t2) = do
  t1' <- rewrite t1
  t2' <- rewrite t2
  return $ TPair t1' t2'
rewrite (TSet t) = do
  t' <- rewrite t
  return $ TSet t
rewrite (TVar v) = do
  (Work _ m _) <- get
  case Map.lookup v m of
    Just t -> case t of 
                TVar v' | Map.member v' m -> rewrite t
                _ -> return t
    Nothing -> return (TVar v)

replace :: Map.Map Var T -> T -> T
replace m (TInt) = TInt
replace m (TBool) = TBool
replace m (TFun t1 t2) = TFun (replace m t1) (replace m t2)
replace m (TPair t1 t2) = TPair (replace m t1) (replace m t2)
replace m (TSet t) = TSet (replace m t)
replace m (TVar v) = m Map.! v

newVar = do 
  (Work l m i) <- get
  put $ Work l m (i+1)
  return $ TVar $ VNumber i

constraint :: T -> T -> State ()
constraint t1 t2 = do 
  (Work l m i) <- get 
  put $ Work (Constraint t1 t2 : l) m (i+1)

substitute :: Var -> T -> State Bool
substitute v t = do
  (Work l m i) <- get
  t' <- rewrite (TVar v)
  t'' <- rewrite t
  case t' of
    (TVar v') -> do
            put $ Work l (Map.insert v' t'' m) i
            return True
    _ -> do
      return (t'' == t')

occurs v (TVar v') = v == v'
occurs v (TSet t) = occurs v t
occurs v (TPair t1 t2) = occurs v t1 || occurs v t2
occurs v (TFun t1 t2) = occurs v t1 || occurs v t2
occurs v _ = False

problem t1 t2 = do
    t1' <- rewrite t1
    t2' <- rewrite t2
    return $ Just
               ("Cannot unify " ++ show t1' ++ " with " ++ show t2')

unify :: T -> T -> State (Maybe String)
unify t1 t2 | t1 == t2 = return Nothing
unify (TVar v) t = if occurs v t 
                   then do
                     return Nothing
                   else do
                     s <- substitute v t
                     if s
                         then return Nothing
                         else problem (TVar v) t
unify t (TVar v) = unify (TVar v) t
unify (TSet t1) (TSet t2) = unify t1 t2
unify (TPair t1 t2) (TPair t3 t4) = do
  unify t2 t4
  unify t1 t3
unify (TFun t1 t2) (TFun t3 t4) = do
  unify t2 t4
  unify t1 t3
unify t1 t2 = problem t1 t2

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
  v1 <- newVar -- TODO EQ types
  v2 <- newVar
  constraint v1 v2
  constraint t TBool
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
        l' <- mapM (\v' -> do v'' <- newVar
                              return (v', v'')) l
        let t'' = replace (Map.fromList l') t'
        constraint t t''
infer env (ELet v e1 e2) t = do return ()
  {-v1 <- newVar
  v2 <- newVar
  infer env e1 v1
  constraint v1 ????
  constraint t v2
  let l = ????
  let env' = Map.insert v (l, v1) env
  infer env' e2 v2-}
infer env (ELambda p e) t  = do return ()
  
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

s = Work [] Map.empty 1
c1 = unify 
     (TFun (TVar $ VName "x") TBool)
     (TFun TInt (TVar $ VName "x"))
c2 = unify 
     (TPair (TVar $ VName "x") $ 
            TPair (TVar $ VName "x") (TVar $ VName "y"))
     (TPair TInt $ TPair (TVar $ VName "z") (TBool))

solve :: State (Maybe String)
solve = do
  Work l m i <- get
  case l of 
    [] -> return Nothing
    Constraint c1 c2 : cs -> do
           put $ Work cs m i
           e <- unify c1 c2
           case e of
             Just v -> return $ Just v
             Nothing -> solve

inf e = do
  let (e, w) = runState aux s
  print w
  case e of 
    Just v -> putStrLn ("Error: " ++ v)
    Nothing -> return ()
  where aux = do
          infer Map.empty e (TVar (VName "res"))
          solve

check c = do
  let (e, w) = runState c s
  print w
  case e of 
    Just v -> putStrLn ("Error: " ++ v)
    Nothing -> return ()
