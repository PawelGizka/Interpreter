module GarbageCollector(performGarbageCollection) where

import Common

import Data.Map
import Data.Array
import Control.Monad.State
import Control.Monad.Reader

import Data.Set (Set)
import qualified Data.Set as Set

type GarbageCollection = ReaderT Store (State (Set Loc)) ()

gcValue :: Value -> GarbageCollection
gcValue value = case value of
  (ValueF (Fun env _ _ _)) -> performGc env
  (ValueA array) -> do
    let elems = Data.Array.elems array
    mapM_ gcValue elems
  _ -> return ()

gcLoc :: Loc -> GarbageCollection
gcLoc loc = do
  store <- ask
  set <- get
  put (Set.insert loc set)
  mapM_ gcValue (Data.Map.lookup loc store)

performGc :: Env -> GarbageCollection
performGc env = do
  set <- get
  let locs = Data.Map.elems env
  let diff = Set.fromList locs Set.\\ set
  mapM_ gcLoc diff

performGarbageCollection :: [Env] -> Store -> Store
performGarbageCollection envs store =
  let reader = runReaderT (mapM_ performGc envs) store
   in let (_, locsVisible) = runState reader Set.empty
       in Data.Map.filterWithKey (\loc _ -> Set.member loc locsVisible) store

