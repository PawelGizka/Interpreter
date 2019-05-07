module TypeCheck (runProgramTypeCheck) where

import AbsMy

import Data.Map

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad

type Var = String

type TypeCheckState = Map Var (Mod, Type)
type TypeCheckEnv = TypeCheckState

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

    (SBlock stms) | not mustBeRet || not (Prelude.null stms) -> checkInNewEnv $ do
      when (length stms > 0) $ do
        mapM_ (\stm -> checkStmType stm funRetType False) (init stms)
        checkStmType (last stms) funRetType mustBeRet

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
      else checkInNewEnv $ do
        setVarType ident MVal Tint
        checkStmType stm funRetType False
    (SForEach (Ident ident1) (Ident ident2) stm) -> do
      (_, typ) <- getVarType ident2
      case typ of
        (TArray arrType) -> checkInNewEnv $ do
          setVarType ident1 MVal arrType
          checkStmType stm funRetType False
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
      checkInNewEnv $ do
        mapM_ (\(ADecl mod (Ident ident) typ) -> setVarType ident mod typ) args
        let funMustHaveReturn = returnType /= Tvoid
        checkStmType stm returnType funMustHaveReturn
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
      when (expType /= Tint) $ throwError $ "Array can be indexed only with Int, but actual type was: " ++ show expType
      when (typ == Tvoid) $ throwError "Cannot create array of void"
      return (TArray typ)
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
    (ENeg exp) -> checkExpOfType exp Tint >> return Tint
    (EMul exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tint
    (EDiv exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tint
    (EPlus exp1 exp2) -> do
      exp1Type <- checkExpType exp1
      exp2Type <- checkExpType exp2
      if exp1Type == exp2Type && exp1Type == Tint then return Tint
      else if exp1Type == TString || exp2Type == TString then return TString
      else throwError $ "Expressions in EPlus must have both type Tint or one of them " ++
                        "must have type Tstring but was " ++ show exp1 ++ " and " ++ show exp2

    (EMinus exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tint
    (ENot exp) -> checkExpOfType exp Tbool >> return Tbool
    (ELt exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (EGt exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (EGtEq exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (ELtEq exp1 exp2) -> checkExpsOfType exp1 exp2 Tint >> return Tbool
    (EEq exp1 exp2) -> checkExpsOfSameTypes exp1 exp2 >> return Tbool
    (ENeq exp1 exp2) -> checkExpsOfSameTypes exp1 exp2 >> return Tbool
    (EAnd exp1 exp2) -> checkExpsOfType exp1 exp2 Tbool >> return Tbool
    (EOr exp1 exp2) -> checkExpsOfType exp1 exp2 Tbool >> return Tbool

checkExpsOfSameTypes :: Exp -> Exp -> TypeCheck ()
checkExpsOfSameTypes exp1 exp2 = do
  exp1Type <- checkExpType exp1
  exp2Type <- checkExpType exp2
  when (exp1Type /= exp2Type) $
    throwError $ "Expressions must have the same type, either " ++ show exp1Type ++ " or " ++ show exp2Type

checkExpsOfType :: Exp -> Exp -> Type -> TypeCheck ()
checkExpsOfType exp1 exp2 typ = checkExpOfType exp1 typ >> checkExpOfType exp2 typ

checkExpOfType :: Exp -> Type -> TypeCheck ()
checkExpOfType exp typ = do
  expType <- checkExpType exp
  when (expType /= typ) $
    throwError $ "Expected expression of type " ++ show typ ++ " but was " ++ show expType ++ " in " ++ show exp

checkInNewEnv :: TypeCheck () -> TypeCheck ()
checkInNewEnv check = do
  env <- ask
  state <- get
  put Data.Map.empty
  let newEnv = Data.Map.union state env
  local (const newEnv) check
  put state

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
checkGlobalFunType (DField _ _ exp@EFun {}) = void (checkExpType exp)
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

runProgramTypeCheck :: Program -> Either String ()
runProgramTypeCheck program =
  case runExcept $
    runStateT (runReaderT (checkProgramType program) initialEnv) Data.Map.empty of
      Right b-> Right ()
      Left a -> Left a

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
  maybe (maybe (throwError $ "Undefined identifier: " ++ v) return fromGlobal) return fromLocal

setVarType :: Var -> Mod -> Type -> TypeCheck ()
setVarType v m t = do
  state <- get
  _ <- put (Data.Map.insert v (m, t) state)
  return ()
