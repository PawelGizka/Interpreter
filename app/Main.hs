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

import TypeCheck

data Fun = Fun [Arg] Type Stm
data Value = ValueS String | ValueI Int | ValueB Bool | ValueF Fun

type Var = String
type Loc = Int
type Store = Map Loc Value
type Env = Map Var Loc
type GlobalEnv = Env

data ComputationState = ComputationState {store :: Store, env :: Env}
emptyComputationState = ComputationState Data.Map.empty Data.Map.empty

type TypeCheck = ReaderT GlobalEnv (StateT ComputationState (Except String))


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
  Ok tree -> runProgramTypeCheck tree

main :: IO ()
main = do
  interact calc
  putStrLn ""
