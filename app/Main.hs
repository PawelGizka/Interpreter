module Main where

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

type Var = String
type Loc = Integer
type Env = Map Var Loc
type GlobalEnv = Env

data Fun = Fun Env [Arg] Type Stm
data Value = ValueS String | ValueI Integer | ValueB Bool | ValueF Fun | ValueA (Array Integer Value) | ValueV

instance Show Value where
  show (ValueS str) = str
  show (ValueI int) = show int
  show (ValueB bool) = show bool
  show (ValueF (Fun _ args returnType _ )) =
    "fun((" ++ show (Prelude.map (\(ADecl mod (Ident ident) typ) -> show mod ++ " " ++ ident ++ ": " ++ show typ) args)
      ++ ") => " ++ show returnType ++ ")"
  show (ValueA arr) = "Array(" ++ show (Prelude.map (\elem -> show elem ++ ",") $ Data.Array.elems arr) ++ ")"

type Store = Map Loc Value

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
    (SBlock stms) -> do
      globalEnv <- ask
      state <- get
      let localEnv = env state
      put (state {env = Data.Map.empty})
      let e = Data.Map.union localEnv globalEnv
      result <- local (const e) $ iterStms stms
      put (state {env = localEnv})
      return result
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
      when (number >= size) $ throwError $ "Array " ++ ident ++
                              " index out of range, array size " ++
                                show size ++ " access " ++ show number

      let newArr = (//) arr [(number, value)]
      reasignVar ident (ValueA newArr)
      return Nothing

    (SExp exp) -> execExp exp >> return Nothing


iterStms :: [Stm] -> Computation (Maybe Value)
iterStms [] = return Nothing
iterStms (h:tail) = do
  result <- execStm h
  case result of
    Nothing -> iterStms tail
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
      globalEnv <- ask
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
        let int = read str :: Integer
        return (ValueI int)
      else do
        funFetched <- getVar ident
        let (ValueF fun) = funFetched
        execFun fun values

    (EArrIni typ exp) -> do
      (ValueI size) <- execExp exp
      let arr = Data.Array.listArray (0, size-1) [ValueV | i <- [0..(size-1)]]
      return (ValueA arr)

    (EArrLen (Ident ident)) -> do
      (ValueA arr) <- getVar ident
      let (_, size) = bounds arr
      return (ValueI (size + 1))

    (EArrAcc (Ident ident) exp) -> do
      (ValueI number) <- execExp exp
      (ValueA arr) <- getVar ident
      let (_, size) = bounds arr
      when (number >= size) $ throwError $ "Array " ++ ident ++
                              " index out of range, array size " ++
                                show size ++ " access " ++ show number
      return (arr Data.Array.! number)

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
  return (ValueB (fun number1 number2))

execBoolExp :: Exp -> Exp -> (Bool -> Bool -> Bool) -> Computation Value
execBoolExp exp1 exp2 fun = do
  (ValueB bool1) <- execExp exp1
  (ValueB bool2) <- execExp exp2
  return (ValueB (fun bool1 bool2))

execNotEqualExp :: Exp -> Exp -> Computation Value
execNotEqualExp exp1 exp2 = do
  (ValueB equal) <- execEqualExp exp1 exp2
  return (ValueB $ not equal)

execEqualExp :: Exp -> Exp -> Computation Value
execEqualExp exp1 exp2 = do
  value1 <- execExp exp1
  value2 <- execExp exp2
  case (value1, value2) of
    (ValueI num1, ValueI num2) -> return (ValueB (num1 == num2))
    (ValueB bool1, ValueB bool2) -> return (ValueB (bool1 == bool2))

execFun :: Fun -> [Value] -> Computation Value
execFun (Fun funEnv funArgs _ stm) args = do
  state <- get
  let localEnv = env state
  put (state {env = Data.Map.empty})
  mapM_ (\(ADecl _ (Ident ident) _, value) -> insertVar ident value) (zip funArgs args)
  returnValue <- local (const funEnv) $ execStm stm
  put (state {env = localEnv})
  return (fromMaybe ValueV returnValue)

execGlobalDefs :: Def -> Computation ()
execGlobalDefs def@(DField _ (Ident ident) exp) = do
  expValue <- execExp exp
  declareDefType def expValue

declareDefType :: Def -> Value -> Computation ()
declareDefType (DField mod (Ident ident) _) value = do
  alreadyDeclared <- isVarDeclared ident
  if alreadyDeclared
    then throwError ("Var already declared" ++ show ident)
    else insertVar ident value

execProgram :: Program -> Computation ()
execProgram (PDefs defs) = do
  mapM_ execGlobalDefs defs --do not check types in functions bodies
  main <- getVar "main"
  let (ValueF mainFun) = main
  let args = Data.Array.listArray (0, 1) [ValueS "program name"]
  void (execFun mainFun [ValueA args])

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
  put (ComputationState (Data.Map.insert nL val st) (Data.Map.insert var nL en) (nL + 1))
  return ()

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
  globalEnv <- ask
  let fromLocal = Data.Map.lookup v localEnv
  let fromGlobal = Data.Map.lookup v globalEnv
  maybe (maybe (throwError $ "Undefined var " ++ v) return fromGlobal) return fromLocal

calc s =
  let ts = myLexer s
  in case pProgram ts of
  Bad s -> "\nParse              Failed...\n Tokens:" ++ show ts ++ "\n " ++ s
  Ok tree -> runProgramTypeCheck tree

main :: IO ()
main = do
  interact calc
  putStrLn ""
