module GarbageCollector(performGarbageCollection) where

import Common

import Data.Map
import Control.Monad.State
import Control.Monad.Reader

import Data.Set (Set)
import qualified Data.Set as Set

gcLoc :: Loc -> ReaderT Store (State (Set Loc)) ()
gcLoc loc = do
  store <- ask
  set <- get
  put (Set.insert loc set)
  case Data.Map.lookup loc store of
    Just (ValueF (Fun env _ _ _)) -> performGc env
    _ -> return ()

performGc :: Env -> ReaderT Store (State (Set Loc)) ()
performGc env = do
  set <- get
  let locs = elems env
  let diff = Set.fromList locs Set.\\ set
  mapM_ gcLoc diff

performGarbageCollection :: [Env] -> Store -> Store
performGarbageCollection envs store =
  let reader = runReaderT (mapM_ performGc envs) store
   in let (_, locsVisible) = runState reader Set.empty
       in Data.Map.filterWithKey (\loc _ -> Set.member loc locsVisible) store

