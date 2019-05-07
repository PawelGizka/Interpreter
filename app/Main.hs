module Main where

import System.Environment

import AbsMy
import LexMy
import ParMy
import ErrM

import Data.Map
import Data.Array
import Data.Maybe

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad

import TypeCheck
import Common
import GarbageCollector
import Text.Read (readMaybe)
import System.IO (hPutStrLn, stderr)


data GlobalEnv = GlobalEnv {all :: [(String, Env)], visible :: Env}

instance Show Value where
  show (ValueS str) = str
  show (ValueI int) = show int
  show (ValueB bool) = show bool
  show (ValueF (Fun _ args returnType _ )) =
    "fun((" ++ show (Prelude.map (\(ADecl mod (Ident ident) typ) -> show mod ++ " " ++ ident ++ ": " ++ show typ) args)
      ++ ") => " ++ show returnType ++ ")"
  show (ValueA arr) = "Array(" ++ show (Prelude.map (\elem -> show elem ++ ",") $ Data.Array.elems arr) ++ ")"

data ComputationState = ComputationState {store :: Store, env :: Env, nextLoc :: Loc}
emptyComputationState = ComputationState Data.Map.empty Data.Map.empty 0

type Computation = ReaderT GlobalEnv (StateT ComputationState (ExceptT String IO))


execStm :: Stm -> Computation (Maybe Value)
execStm stm =
  case stm of
    (SReturnE exp) -> do
      value <- execExp exp
      return $ Just value
    SReturn -> return (Just ValueV)
    (SBlock stms) -> execStmInNewEnv "Block" $ iterStms stms
    (SIfElse exp stm1 stm2) -> do
      (ValueB cond) <- execExp exp
      if cond
        then execStm stm1
        else execStm stm2

    (SEAsign (Ident ident) exp) -> do
      value <- execExp exp
      reasignVar ident value
      return Nothing

    (SArrAsign (Ident ident) exp1 exp2) -> do
      (ValueI number) <- execExp exp1
      value <- execExp exp2
      (ValueA arr) <- getVar ident
      let (_, size) = bounds arr
      when (number >= (size+1)) $ throwError $ "Array " ++ ident ++
                              " index out of range, array size " ++
                                show (size+1) ++ " access " ++ show number

      let newArr = (//) arr [(number, value)]
      reasignVar ident (ValueA newArr)
      return Nothing

    (SExp exp) -> execExp exp >> return Nothing
    (SDef def) -> execDef def >> return Nothing
    (SInc (Ident ident)) -> do
      (ValueI num) <- getVar ident
      reasignVar ident (ValueI (num+1))
      return Nothing
    (SDec (Ident ident)) -> do
      (ValueI num) <- getVar ident
      reasignVar ident (ValueI (num-1))
      return Nothing
    (SWhile exp stm) -> iterWhile exp stm
    (SFor (Ident ident) exp1 exp2 stm) -> execStmInNewEnv "For" $ do
      (ValueI from) <- execExp exp1
      (ValueI to) <- execExp exp2
      insertVar ident (ValueI (from - 1))
      iterFor to ident stm

    (SForEach (Ident ident1) (Ident ident2) stm) -> execStmInNewEnv "Foreach"$ do
      (ValueA arr) <- getVar ident2
      insertVar ident1 ValueV
      iterForEach (Data.Array.elems arr) stm ident1

    (SIf exp stm) -> do
      (ValueB cond) <- execExp exp
      if cond
        then execStm stm
        else return Nothing

execStmInNewEnv :: String -> Computation (Maybe Value) -> Computation (Maybe Value)
execStmInNewEnv stmName comp = do
  globalEnv <- ask
  state <- get
  let localEnv = env state
  put (state {env = Data.Map.empty})
  let e = Data.Map.union localEnv (visible globalEnv)
  let newGlobalEnv = GlobalEnv ((stmName, localEnv) : Main.all globalEnv) e
  result <- local (const newGlobalEnv) comp
  changedState <- get
  put (changedState {env = localEnv})
  return result

iterStms :: [Stm] -> Computation (Maybe Value)
iterStms [] = return Nothing
iterStms (h:tail) = do
  result <- execStm h
  case result of
    Nothing -> iterStms tail
    r@(Just _) -> return r

iterWhile :: Exp -> Stm -> Computation (Maybe Value)
iterWhile exp stm = do
  (ValueB cond) <- execExp exp
  if cond
    then do
      value <- execStm stm
      case value of
        Nothing -> iterWhile exp stm
        r@(Just _) -> return r
    else return Nothing

iterFor :: Integer -> Var -> Stm -> Computation (Maybe Value)
iterFor to var stm = do
  (ValueI num) <- getVar var
  reasignVar var (ValueI (num+1))
  if num+1 <= to then do
    value <- execStm stm
    case value of
      Nothing -> iterFor to var stm
      r@(Just _) -> return r
  else return Nothing

iterForEach :: [Value] -> Stm -> Var -> Computation (Maybe Value)
iterForEach [] _  _ = return Nothing
iterForEach (h:tail) stm ident = do
  result <- case h of
    ValueV -> return Nothing --skip not initialized elements
    _ -> do
      reasignVar ident h
      execStm stm

  case result of
    Nothing -> iterForEach tail stm ident
    r@(Just _) -> return r

execExp :: Exp -> Computation Value
execExp exp =
  case exp of
    (EHi exp) -> execExp exp
    (EIdent (Ident ident)) -> getVar ident
    (EInt int) -> return (ValueI int)
    (EString str) -> return (ValueS str)
    ETrue -> return (ValueB True)
    EFalse -> return (ValueB False)
    (EFun args returnType stm) -> do
      globalEnv <- asks visible
      localEnv <- gets env
      let funEnv = Data.Map.union localEnv globalEnv
      return (ValueF $ Fun funEnv args returnType stm)
    (EAppFun (Ident ident) exps) -> do
      values <- mapM execExp exps
      if ident == "printString" then do
        let (ValueS string) = head values
        liftIO $ putStrLn string
        return ValueV
      else if ident == "printInt" then do
        let (ValueI int) = head values
        liftIO $ print int
        return ValueV
      else if ident == "readString" then do
        str <- liftIO getLine
        return (ValueS str)
      else if ident == "readInt" then do
        str <- liftIO getLine
        let parsed = readMaybe str :: Maybe Integer
        case parsed of
          Just int -> return (ValueI int)
          Nothing -> throwError $ "readInt error, expected int but was " ++ str
      else do
        funFetched <- getVar ident
        let (ValueF fun) = funFetched
        execFun ident fun values

    (EArrIni typ exp) -> do
      (ValueI size) <- execExp exp
      let arr = Data.Array.listArray (0, size-1) [ValueV | i <- [0..(size-1)]]
      return (ValueA arr)

    (EArrLen (Ident ident)) -> do
      (ValueA arr) <- getVar ident
      let (_, size) = bounds arr
      return (ValueI (size+1))

    (EArrAcc (Ident ident) exp) -> do
      (ValueI number) <- execExp exp
      (ValueA arr) <- getVar ident
      let (_, size) = bounds arr
      when (number >= (size+1)) $ throwError $ "Array " ++ ident ++
                              " index out of range, array size " ++
                                show (size+1) ++ " access " ++ show number
      let elem = arr Data.Array.! number
      when (elem == ValueV) $ throwError $ "Array " ++ ident ++
                            " element of index " ++ show number ++ " was not initialized"
      return elem

    (ENeg exp) -> do
      (ValueI number) <- execExp exp
      return (ValueI (-number))

    (EMul exp1 exp2) -> do
      (ValueI number1) <- execExp exp1
      (ValueI number2) <- execExp exp2
      return (ValueI $ number1 * number2)

    (EDiv exp1 exp2) -> do
      (ValueI number1) <- execExp exp1
      (ValueI number2) <- execExp exp2
      when (number2 == 0) $ throwError $ "Division " ++ show number1 ++ " by 0"
      return (ValueI $ quot number1  number2)

    (EPlus exp1 exp2) -> do
      value1 <- execExp exp1
      value2 <- execExp exp2
      case (value1, value2) of
        (ValueI num1, ValueI num2) -> return (ValueI $ num1 + num2)
        _ -> return (ValueS $ show value1 ++ show value2)

    (EMinus exp1 exp2) -> do
      (ValueI number1) <- execExp exp1
      (ValueI number2) <- execExp exp2
      return (ValueI $ number1 - number2)

    (ENot exp) -> do
      (ValueB bool) <- execExp exp
      return (ValueB (not bool))

    (ELt exp1 exp2) -> execIntExp exp1 exp2 (<)
    (EGt exp1 exp2) -> execIntExp exp1 exp2 (>)
    (EGtEq exp1 exp2) -> execIntExp exp1 exp2 (<=)
    (ELtEq exp1 exp2) -> execIntExp exp1 exp2 (>=)
    (EEq exp1 exp2) -> execEqualExp exp1 exp2
    (ENeq exp1 exp2) -> execNotEqualExp exp1 exp2
    (EAnd exp1 exp2) -> execBoolExp exp1 exp2 (&&)
    (EOr exp1 exp2) -> execBoolExp exp1 exp2 (||)

execIntExp :: Exp -> Exp -> (Integer -> Integer -> Bool) -> Computation Value
execIntExp exp1 exp2 fun = do
  (ValueI number1) <- execExp exp1
  (ValueI number2) <- execExp exp2
  return (ValueB (fun number2 number1))

execBoolExp :: Exp -> Exp -> (Bool -> Bool -> Bool) -> Computation Value
execBoolExp exp1 exp2 fun = do
  (ValueB bool1) <- execExp exp1
  (ValueB bool2) <- execExp exp2
  return (ValueB (fun bool2 bool1))

execNotEqualExp :: Exp -> Exp -> Computation Value
execNotEqualExp exp1 exp2 = do
  (ValueB equal) <- execEqualExp exp1 exp2
  return (ValueB $ not equal)

execEqualExp :: Exp -> Exp -> Computation Value
execEqualExp exp1 exp2 = do
  value1 <- execExp exp1
  value2 <- execExp exp2
  return (ValueB (value1 == value2))

execFun :: String -> Fun -> [Value] -> Computation Value
execFun funName (Fun funEnv funArgs _ stm) args = do
  state <- get
  globalEnv <- ask
  let localEnv = env state
  put (state {env = Data.Map.empty})
  mapM_ (\(ADecl _ (Ident ident) _, value) -> insertVar ident value) (zip funArgs args)
  let newGlobalEnv = GlobalEnv (("Function: " ++ funName, funEnv) : Main.all globalEnv) funEnv
  returnValue <- local (const newGlobalEnv) $ execStm stm
  changedState <- get
  put (changedState {env = localEnv})
  return (fromMaybe ValueV returnValue)

execDef :: Def -> Computation ()
execDef def@(DField _ (Ident ident) exp) = do
  alreadyDeclared <- isVarDeclared ident
  if alreadyDeclared
    then throwError ("Var already declared" ++ show ident)
    else do
      value <- execExp exp
      case value of
        (ValueF (Fun env args returnType stm)) -> do
          loc <- gets nextLoc
          let newEnv = Data.Map.insert ident loc env
          --remember funtion loc to allow recursion
          insertVar ident (ValueF (Fun newEnv args returnType stm))
        _ -> insertVar ident value

isVarDeclared :: Var -> Computation Bool
isVarDeclared v = do
  env <- gets env
  case Data.Map.lookup v env of
    Just _ -> return True
    Nothing -> return False

getVar :: Var -> Computation Value
getVar v = do
  store <- gets store
  loc <- getVarLoc v
  maybe (throwError $ "Undefined loc " ++ show loc ++ " of " ++ v) return (Data.Map.lookup loc store)
--
insertVar :: Var -> Value -> Computation ()
insertVar var val = do
  state <- get
  let en = env state
  let st = store state
  let nL = nextLoc state
  let newStore = Data.Map.insert nL val st
  let newEnv = Data.Map.insert var nL en
  put (ComputationState newStore newEnv (nL + 1))
  when (rem (nL + 1) 1000000 == 0) $ do
    allGlobal <- asks Main.all
    let allGlobalEnvs = Prelude.map snd allGlobal
    let garbageCollectedStore = performGarbageCollection (newEnv : allGlobalEnvs) newStore
    put (ComputationState garbageCollectedStore newEnv (nL + 1))

reasignVar :: Var -> Value -> Computation()
reasignVar var val = do
  store <- gets store
  state <- get
  loc <- getVarLoc var
  put (state {store = Data.Map.insert loc val store})
  return ()

getVarLoc :: Var -> Computation Loc
getVarLoc v = do
  localEnv <- gets env
  globalEnv <- asks visible
  let fromLocal = Data.Map.lookup v localEnv
  let fromGlobal = Data.Map.lookup v globalEnv
  maybe (maybe (throwError $ "Undefined var " ++ v) return fromGlobal) return fromLocal

execProgram :: Program -> [String] -> Computation ()
execProgram (PDefs defs) args = do
  mapM_ execDef defs
  globalEnv <- gets env
  forM_ (Data.Map.keys globalEnv) $ \name -> do
    value <- getVar name
    case value of
      (ValueF fun@(Fun env args returnType stm)) -> reasignVar name (ValueF (Fun globalEnv args returnType stm))
      _ -> return ()
    return ()
  main <- getVar "main"
  let (ValueF mainFun) = main
  let parsedArgs = Data.Array.listArray (0, toInteger $ length args - 1) (Prelude.map ValueS args)
  void (execFun "main" mainFun [ValueA parsedArgs])

exec :: Program -> [String] -> IO ()
exec program args = do
  result <- runExceptT $ runStateT (runReaderT (execProgram program args) (GlobalEnv [] Data.Map.empty)) emptyComputationState
  case result of
    Right b -> putStrLn "program completed successfully"
    Left a -> hPutStrLn stderr $ "RUNTIME: " ++ a

checkCorrectness :: String -> Either String Program
checkCorrectness s =
  let ts = myLexer s
  in case pProgram ts of
  Bad s -> Left $ "Parsing error\n Tokens:" ++ show ts ++ "\n " ++ s
  Ok tree ->
    case runProgramTypeCheck tree of
      Right _ -> Right tree
      Left e -> Left e

main :: IO ()
main = do
  args <- getArgs
  if length args == 0
    then putStrLn "you must supply program to run as argument"
    else do
      s <- readFile $ head args
      case checkCorrectness s of
        (Left error) -> hPutStrLn stderr error
        (Right program) -> exec program args
