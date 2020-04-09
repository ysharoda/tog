{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.TGraphTest
  ( computeGraph 
  , graph
  ) where

import qualified Data.Map            as Map
import           Control.Lens ((^.), makeLenses, over)

import           Tog.Deriving.Lenses (name)
import           Tog.Deriving.TUtils (mkName, mkField)
import           Tog.Deriving.Types
import           Tog.Deriving.TGraph
import           Tog.Raw.Abs         as Abs

data Graph = Graph {
  _graph   :: TGraph,
  _renames :: Map.Map Name_ Rename }

makeLenses ''Graph

initGraph :: Graph 
initGraph = Graph emptyTG (Map.empty) 

computeGraph :: [Abs.Language] ->  Graph 
computeGraph = foldl add initGraph

add :: Graph -> Abs.Language -> Graph
add g (TheoryC nm clist)  = theory  nm clist g
add g (MappingC nm vlist) = renList nm vlist g
add g (ModExprC nm mexps) = modExpr nm mexps g

theory :: Name -> [Abs.Constr] -> Graph -> Graph
theory nm cList = over graph (over nodes (Map.insert (nm^.name) newThry))
  where newThry  = GTheory NoParams $ mkField cList

renList :: Name -> Rens -> Graph -> Graph
renList nm rens gs = 
  over renames (Map.insert (nm^.name) (rensToRename gs rens)) gs

getTheory :: Graph -> Name -> GTheory
getTheory gs n = lookupName (n^.name) (gs^.graph)

modExpr :: Name -> Abs.ModExpr -> Graph -> Graph
modExpr nam mexpr gs =
  let n = nam^.name
      look = getTheory gs
      rens = rensToRename gs
      combineOver t1 r1 t2 r2 s =
        let gr = gs^.graph
            p1 = getPath gr s t1
            p2 = getPath gr s t2
            qpath1 = QPath p1 $ rens r1
            qpath2 = QPath p2 $ rens r2
        in over graph
           (updateGraph n $ Right $ computeCombine qpath1 qpath2) gs    
  in case mexpr of
    Extend srcName clist ->
      over graph
        (updateGraph n $ Left $ computeExtend clist (look srcName)) gs
    Rename srcName rlist ->   
      over graph
        (updateGraph n $ Left $ computeRename (rens rlist) (look srcName)) gs
    RenameUsing srcName nm ->
     let mapin = (gs^.renames) Map.! (nm^.name) 
     in over graph
        (updateGraph n $ Left $ computeRename mapin (look srcName))
        gs
    CombineOver t1 r1 t2 r2 srcName ->
     let s = look srcName
     in combineOver (look t1) r1 (look t2) r2 s 
    Combine t1 t2 ->
     let s = findApex (gs^.graph) (look t1) (look t2)
     in combineOver (look t1) NoRens (look t2) NoRens s
    Transport t1 t2 -> 
     let s = findApex (gs^.graph) (look t1) (look t2)
     in combineOver (look t1) NoRens (look t2) NoRens s

rensToRename :: Graph -> Rens -> Rename
rensToRename gs (NameRens n) = (gs^.renames) Map.! (n^.name)
rensToRename _  NoRens = Map.empty
rensToRename _ (Rens rlist) = Map.fromList $ map (\(RenPair x y) -> (x^.name,y^.name)) rlist
