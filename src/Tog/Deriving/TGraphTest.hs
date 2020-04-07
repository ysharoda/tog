{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.TGraphTest
  ( computeGraph 
  , graphNodes
  ) where

import qualified Data.Map            as Map
import           Control.Lens ((^.), makeLenses, view, over)

import           Tog.Deriving.Lenses (name)
import           Tog.Deriving.TUtils (mkName, mkField)
import           Tog.Deriving.Types
import           Tog.Deriving.TGraph
import           Tog.Raw.Abs         as Abs

data Graph = Graph {
  _graph   :: TGraph,
  _renames :: Map.Map Name_ Rename }

makeLenses ''Graph

graphNodes :: Graph -> Map.Map Name_ GTheory
graphNodes = view (graph . nodes)

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
  let n = nam^.name in
  let look = getTheory gs in
  let rens = rensToRename gs
  case mexpr of
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
    CombineOver trgt1 ren1 trgt2 ren2 srcName ->
     let s = look srcName
         gr = gs^.graph
         p1 = getPath gr s $ look trgt1
         p2 = getPath gr s $ look trgt2
         qpath1 = QPath p1 $ rens ren1
         qpath2 = QPath p2 $ rens ren2
     in over graph
        (updateGraph n $ Right $ computeCombine qpath1 qpath2) gs
    Combine trgt1 trgt2 ->
      modExpr nam
        (Abs.CombineOver trgt1 NoRens trgt2 NoRens (mkName "Carrier")) gs
          -- TODO: (computeCommonSource name1 name2)
    Transport nn srcName -> -- Transport amounts to renaming
     over graph
      (updateGraph n $ Left $ computeRename (rens nn) $ look srcName)
      gs

rensToRename :: Graph -> Rens -> Rename
rensToRename gs (NameRens n) = (gs^.renames) Map.! (n^.name)
rensToRename _  NoRens = Map.empty
rensToRename _ (Rens rlist) = Map.fromList $ map (\(RenPair x y) -> (x^.name,y^.name)) rlist
