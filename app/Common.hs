module Common where

import Data.Map
import AbsMy
import Data.Array

data Fun = Fun Env [Arg] Type Stm deriving(Eq)
data Value = ValueS String | ValueI Integer | ValueB Bool | ValueF Fun | ValueA (Array Integer Value) | ValueV deriving(Eq)

type Var = String
type Loc = Integer
type Env = Map Var Loc
type Store = Map Loc Value


