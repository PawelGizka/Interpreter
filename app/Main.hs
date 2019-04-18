module Main where

import AbsMy
import LexMy
import ParMy
import ErrM

import Data.Map

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad

data Fun = Fun [Arg] Type Stm
data Value = ValueS String | ValueI Int | ValueB Bool | ValueF Fun

type Var = String
type Loc = Int
type Store = Map Loc Value
type Env = Map Var Loc

data ComputationState = ComputationState {store :: Store, env :: Env}
emptyComputationState = ComputationState Data.Map.empty Data.Map.empty

type TypeCheckState = Map Var (Mod, Type)
type TypeCheckEnv = TypeCheckState

type Computation = StateT ComputationState (Except String)
type TypeCheck = ReaderT TypeCheckEnv (StateT TypeCheckState (Except String))


checkStmType :: Stm -> Type -> Bool -> TypeCheck ()
checkStmType stm funRetType mustBeRet =
  case stm of
    (SReturnE exp) -> do
      expType <- checkExpType exp
      when (funRetType /= expType) $
        throwError $ "Function has got return type " ++ show funRetType ++ " but actual was " ++ show expType

    SReturn ->
      when (funRetType /= Tvoid) $
      throwError $ "Function has got return type " ++ show funRetType ++ " but actual was Tvoid"

    (SBlock stms) | not mustBeRet || not (Prelude.null stms) -> do
      env <- ask
      state <- get
      put Data.Map.empty
      let newEnv = Data.Map.union state env
      when (length stms > 0) $
        local (const newEnv) $ mapM_ (\stm -> checkStmType stm funRetType False) (init stms) >>
        checkStmType (last stms) funRetType mustBeRet
      put state

    (SIfElse exp stm1 stm2) -> do
      expType <- checkExpType exp
      if expType /= Tbool
        then throwError $ "Expression in if must be Tbool but was " ++ show expType
        else checkStmType stm1 funRetType mustBeRet >> checkStmType stm2 funRetType mustBeRet

    _ | mustBeRet -> throwError "No return statment in function body"

    (SEAsign (Ident ident) exp) -> do
      (mod, typ) <- getVarType ident
      expType <- checkExpType exp
      if mod == MVal
        then throwError $ ident ++ " is not assignable"
        else when (expType /= typ) $
             throwError $ ident ++ " has type " ++ show typ ++ " but " ++ show expType ++ " was assigned"
    (SArrAsign (Ident ident) exp1 exp2) -> do
      (mod, typ) <- getVarType ident
      exp1Type <- checkExpType exp1
      exp2Type <- checkExpType exp2
      case typ of
        (TArray arrType)
          | exp1Type /= Tint -> throwError $ "Array access exp must be Tint but was " ++ show exp1Type
          | arrType /= exp2Type ->
            throwError $ "Array " ++ ident ++ " has type " ++ show typ ++ " but was asssigned to " ++ show exp2Type
          | otherwise -> return ()
        _ -> throwError $ ident ++ " is not an array"
    (SExp exp) -> void (checkExpType exp)
    (SDef def) -> checkDefType def
    (SInc (Ident ident)) -> checkIntIncDecStm ident
    (SDec (Ident ident)) -> checkIntIncDecStm ident
    (SWhile exp stm) -> do
      expType <- checkExpType exp
      if expType /= Tbool
        then throwError $ "Expression in While must be Tbool but was " ++ show expType
        else checkStmType stm funRetType False
    (SFor (Ident ident) exp1 exp2 stm) -> do
      exp1Type <- checkExpType exp1
      exp2Type <- checkExpType exp2
      if exp1Type /= Tint
        then throwError $ "Expression in For must have type Tint but was " ++ show exp1Type
        else if exp2Type /= Tint
               then throwError $ "Expression in For must have type Tint but was " ++ show exp2Type
               else do
                 env <- ask
                 state <- get
                 put Data.Map.empty
                 setVarType ident MVal Tint
                 let newEnv = Data.Map.union state env
                 local (const newEnv) $ checkStmType stm funRetType False
                 put state
    (SForEach (Ident ident1) (Ident ident2) stm) -> do
      (_, typ) <- getVarType ident2
      case typ of
        (TArray arrType) -> do
          env <- ask
          state <- get
          put Data.Map.empty
          setVarType ident1 MVal arrType
          let newEnv = Data.Map.union state env
          local (const newEnv) $ checkStmType stm funRetType False
          put state
        _ -> throwError $ "Can iterate only through array, but was" ++ show typ
    (SIf exp stm) -> do
      expType <- checkExpType exp
      if expType /= Tbool
        then throwError $ "Expression in if must be Tbool but was " ++ show expType
        else checkStmType stm funRetType False

checkIntIncDecStm :: Var -> TypeCheck ()
checkIntIncDecStm ident = do
  (mod, typ) <- getVarType ident
  if mod == MVal
    then throwError $ ident ++ " is not assignable"
    else when (typ /= Tint) $
         throwError $ ident ++ " has type " ++ show typ ++ " but only Tint can be incremented/decremented"

checkExpType :: Exp -> TypeCheck Type
checkExpType exp =
  case exp of
    (EHi exp) -> checkExpType exp
    (EIdent (Ident ident)) -> do
      varTypePair <- getVarType ident
      return $ snd varTypePair
    (EInt _) -> return Tint
    (EString _) -> return TString
    ETrue -> return Tbool
    EFalse -> return Tbool
    (EFun args returnType stm) -> do
      env <- ask
      state <- get
      put Data.Map.empty
      mapM_ (\(ADecl mod (Ident ident) typ) -> setVarType ident mod typ) args
      let newEnv = Data.Map.union state env
      let funMustHaveReturn = returnType /= Tvoid
      local (const newEnv) $ checkStmType stm returnType funMustHaveReturn
      put state
      let types = Prelude.map (\(ADecl _ _ typ) -> typ) args
      return (TFun types returnType)
    (EAppFun (Ident ident) exps) -> do
      expTypes <- mapM checkExpType exps
      (funMod, funType) <- getVarType ident
      case funType of
        (TFun types returnType) ->
          if length types /= length expTypes
            then throwError $
                 "function: " ++
                 ident ++ " takes " ++ show (length types) ++ " arguments, but applied to " ++ show (length expTypes)
            else do
              let zipped = zip types expTypes
              mapM_
                (\(expected, actual) ->
                   Control.Monad.when (expected /= actual) $
                   throwError $
                   "function " ++
                   ident ++ " apply error, expected type: " ++ show expected ++ " actual: " ++ show actual)
                zipped
              return returnType
        _ -> throwError $ ident ++ " is not a function"
    (EArrIni typ exp) -> do
      expType <- checkExpType exp
      if expType /= Tint
        then throwError $ "Array can be initiated only with Int, but actual type was: " ++ show expType
        else return (TArray expType)
    (EArrLen (Ident ident)) -> do
      (mod, typ) <- getVarType ident
      case typ of
        (TArray _) -> return Tint
        _ -> throwError $ "Length can be accessed only from array, but actual " ++ ident ++ " type was " ++ show typ
    (EArrAcc (Ident ident) exp) -> do
      (mod, typ) <- getVarType ident
      expType <- checkExpType exp
      if expType /= Tint
        then throwError $ "Array can access exprestion must Int but was: " ++ show expType
        else case typ of
               (TArray arrType) -> return arrType
               _ -> throwError $ "Array access on " ++ ident ++ " of type " ++ show typ
    (ENeg exp) -> checkExpOfType exp Tint
    (EMul exp1 exp2) -> checkExpsOfType exp1 exp2 Tint
    (EDiv exp1 exp2) -> checkExpsOfType exp1 exp2 Tint
    (EPlus exp1 exp2) -> do
      exp1Type <- checkExpType exp1
      exp2Type <- checkExpType exp2
      if exp1Type == exp2Type && exp1Type == Tint then return Tint
      else if exp1Type == TString || exp2Type == TString then return TString
      else throwError $ "Expressions in EPlus must have both type Tint or one of them " ++
                        "must have type Tstring but was " ++ show exp1 ++ " and " ++ show exp2

    (EMinus exp1 exp2) -> checkExpsOfType exp1 exp2 Tint
    (ENot exp) -> checkExpOfType exp Tint
    (ELt exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (EGt exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (EGtEq exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (ELtEq exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (EEq exp1 exp2) -> checkExpsOfTypes exp1 exp2 Tint Tbool
    (ENeq exp1 exp2) -> checkExpsOfTypes exp1 exp2 Tint Tbool
    (EAnd exp1 exp2) -> checkExpsOfType exp1 exp2 Tbool >> return Tbool
    (EOr exp1 exp2) -> checkExpsOfType exp1 exp2 Tbool >> return Tbool

checkExpsOfTypes :: Exp -> Exp -> Type -> Type -> TypeCheck Type
checkExpsOfTypes exp1 exp2 type1 type2 = do
  exp1Type <- checkExpType exp1
  exp2Type <- checkExpType exp2
  if exp1Type /= exp2Type || (exp1Type /= type1 && exp1Type /= type2)
    then throwError $ "Expressions must have the same type, either " ++ show exp1 ++ " or " ++ show exp2
    else return exp1Type

checkExpsOfType :: Exp -> Exp -> Type -> TypeCheck Type
checkExpsOfType exp1 exp2 typ = checkExpOfType exp1 typ >> checkExpOfType exp2 typ

checkExpOfType :: Exp -> Type -> TypeCheck Type
checkExpOfType exp typ= do
  expType <- checkExpType exp
  if expType /= typ
    then throwError $ "Expected expression of type " ++ show typ ++ " but was " ++ show expType ++ " in " ++ show exp
    else return Tint

checkDefType :: Def -> TypeCheck ()
checkDefType def@(DField _ _ exp@(EFun args returnType _)) = do
  --function name must be in scope before checking function body
  --to allow recursion
  let argsTypes = Prelude.map (\(ADecl _ _ typ) -> typ) args
  let funType = TFun argsTypes returnType
  declareDefType def funType
  void (checkExpType exp)
checkDefType def@(DField _ _ exp) = checkExpType exp >>= declareDefType def

checkGlobalDefType :: Def -> TypeCheck ()
checkGlobalDefType def@(DField mod (Ident ident) exp) = do
  expType <- case exp of
    --do not check types in functions bodies
    (EFun args returnType _) ->
      let types = Prelude.map (\(ADecl _ _ typ) -> typ) args
      in return (TFun types returnType)
    _ -> checkExpType exp
  declareDefType def expType

declareDefType :: Def -> Type -> TypeCheck ()
declareDefType (DField mod (Ident ident) _) expType = do
  alreadyDeclared <- isVarDeclared ident
  if alreadyDeclared
    then throwError ("Var already declared" ++ show ident)
    else setVarType ident mod expType

checkGlobalFunType :: Def -> TypeCheck ()
checkGlobalFunType (DField _ _ exp@EFun {}) = checkExpType exp >> return ()
checkGlobalFunType _ = return ()

checkProgramType :: Program -> TypeCheck ()
checkProgramType (PDefs defs) = do
  mapM_ checkGlobalDefType defs --do not check types in functions bodies
  mapM_ checkGlobalFunType defs --now check types in functions bodies

initialEnv = Data.Map.fromList [
  ("printString", (MVal, TFun [TString] Tvoid)),
  ("printInt", (MVal, TFun [Tint] Tvoid)),
  ("readString", (MVal, TFun [] TString)),
  ("readInt", (MVal, TFun [] Tint))
  ]

runProgramCheck :: Program -> String
runProgramCheck program = case runExcept $ runStateT (runReaderT (checkProgramType program) initialEnv) Data.Map.empty of
  Right b-> "ok"
  Left a -> show a

isVarDeclared :: Var -> TypeCheck Bool
isVarDeclared v = do
  state <- get
  case Data.Map.lookup v state of
    Just _ -> return True
    Nothing -> return False

getVarType :: Var -> TypeCheck (Mod, Type)
getVarType v = do
  state <- get
  env <- ask
  let fromLocal = Data.Map.lookup v state
  let fromGlobal = Data.Map.lookup v env
  maybe (maybe (throwError $ "Undefined var " ++ v) return fromGlobal) return fromLocal

setVarType :: Var -> Mod -> Type -> TypeCheck ()
setVarType v m t = do
  state <- get
  _ <- put (Data.Map.insert v (m, t) state)
  return ()

--setVar :: ComputationState -> Var -> Value -> ComputationState
--
--getVar :: Var -> Computation Value
--getVar v = do
--  state <- get
--  let r = fetchVar v state
--  maybe (throwError $ "Undefined var " ++ v) return r
--
--fetchVar :: Var -> ComputationState -> Maybe Value
--fetchVar v s = do
-- let environment = env s
-- let storeF = store s
-- loc <- Data.Map.lookup v environment
-- Data.Map.lookup loc storeF

--checkTypes :: Program -> String
--checkTypes PDefs defs = runStateT

calc s =
  let ts = myLexer s
  in case pProgram ts of
  Bad s -> "\nParse              Failed...\n Tokens:" ++ show ts ++ "\n " ++ s
  Ok tree -> runProgramCheck tree

main :: IO ()
main = do
  interact calc
  putStrLn ""
