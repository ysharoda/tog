module Tog.Deriving.TGraphTest
  ( computeGraph 
  , createModules -- used in Algebra
  , graphNodes    -- used in Algebra
  ) where

import qualified Data.Map            as Map

import           Tog.Deriving.Types
import           Tog.Deriving.TGraph
import           Tog.Deriving.TUtils (mkName, name_)
import           Tog.Raw.Abs         as Abs

moduleName :: String
moduleName = "MathScheme" 

data Graph = Graph {
  graph   :: TGraph,
  renames :: Map.Map Name_ Rename }

graphNodes :: Graph -> Map.Map Name_ GTheory
graphNodes = nodes . graph

graphEdges :: Graph -> Map.Map Name_ GView
graphEdges = edges . graph

initGraph :: Graph 
initGraph = Graph (TGraph Map.empty Map.empty) (Map.empty) 

computeGraph :: [Abs.Language] ->  Graph 
computeGraph = foldl add initGraph

add :: Graph -> Abs.Language -> Graph
add g (TheoryC name clist)  = theory  g name clist
add g (MappingC name vlist) = renList g name vlist
add g (ModExprC name mexps) = modExpr g name mexps

theory :: Graph -> Name -> [Abs.Constr] -> Graph
theory gs thryName cList =
  Graph  
   (TGraph (Map.insert (name_ thryName) newThry $ graphNodes gs) (graphEdges gs))
   (renames gs) 
  where newThry  = (GTheory NoParams $ flds cList)
        flds [] = NoFields
        flds ls = Fields ls              

renList :: Graph -> Name -> Rens -> Graph 
renList gs name rens =
  gs { renames = Map.insert (name_ name) (rensToRename gs rens) (renames gs) }

getTheory :: Name -> Graph -> GTheory
getTheory n gs = lookupName (name_ n) (graph gs)

modExpr :: Graph -> Name -> Abs.ModExpr -> Graph
modExpr gs name mexpr =
  case mexpr of
    Extend srcName clist ->
      Graph (updateGraph (graph gs) (name_ name) $ Left $ computeExtend clist (getTheory srcName gs))
        (renames gs)
    Rename srcName rlist ->   
      Graph
        (updateGraph (graph gs) (name_ name) $ Left $ computeRename (rensToRename gs rlist) (getTheory srcName gs))
        (renames gs)
    RenameUsing srcName mapName ->
     let mapin = (renames gs) Map.! (name_ mapName) 
     in Graph
        (updateGraph (graph gs) (name_ name) $ Left $ computeRename mapin (getTheory srcName gs))
        (renames gs)
    CombineOver trgt1 ren1 trgt2 ren2 srcName ->
     let s = getTheory srcName gs
         gr = graph gs
         p1 = getPath gr s $ getTheory trgt1 gs
         p2 = getPath gr s $ getTheory trgt2 gs
         qpath1 = QPath p1 $ rensToRename gs ren1
         qpath2 = QPath p2 $ rensToRename gs ren2
     in Graph
        (updateGraph gr (name_ name) $ Right $ computeCombine qpath1 qpath2)
        (renames gs)  
    Combine trgt1 trgt2 ->
      modExpr gs name $
        Abs.CombineOver trgt1 NoRens trgt2 NoRens (Name ((0,0),"Carrier"))
          -- TODO: (computeCommonSource name1 name2)
    Transport n srcName ->
     Graph
      (updateGraph (graph gs) (name_ name) $ Left $ computeTransport (rensToRename gs n) $ getTheory srcName gs)
      (renames gs) 

rensToRename :: Graph -> Rens -> Rename
rensToRename gs (NameRens n) = (renames gs) Map.! (name_ n)
rensToRename _  NoRens = Map.empty
rensToRename _ (Rens rlist) = Map.fromList $ map (\(RenPair x y) -> (name_ x,name_ y)) rlist

{- ------------------------------------------------------------- -} 

theoryToRecord :: Name_ -> GTheory -> Decl 
theoryToRecord thryName (GTheory ps fs) =
  Record (mkName thryName) ps
         (RecordDeclDef (mkName "Set") (mkName $ thryName++"C") fs)  

recordToModule :: Name_ -> Decl -> Decl
recordToModule thryName record =
  Module_ $ Module (mkName thryName) NoParams $ Decl_ [record] 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module (mkName moduleName) NoParams $ Decl_ $ Map.elems modules 
