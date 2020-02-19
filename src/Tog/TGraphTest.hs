module Tog.TGraphTest where

import qualified Data.Map        as Map

import           Tog.TGraph      as TGraph
import           Tog.Raw.Abs     as Abs

getName :: Name -> String
getName (Name (_,str)) = str

moduleName :: String
moduleName = "MathScheme" 

data GraphState = GraphState{
  graph   :: TGraph,
  renames :: (Map.Map Name_ Mapping)}

graphNodes :: GraphState -> Map.Map Name_ GTheory
graphNodes gs = nodes $ graph gs

graphEdges :: GraphState -> Map.Map Name_ GView
graphEdges gs = edges $ graph gs

initGraphState :: GraphState 
initGraphState =
  GraphState (TGraph Map.empty Map.empty) (Map.empty) 

computeGraphState :: [Abs.Language] ->  GraphState 
computeGraphState defs = 
  foldl updateState initGraphState defs

-- data LangExt = MExprC ModExpr | TheoryC Theory | RenLC RenList
updateState :: GraphState -> Abs.Language -> GraphState
updateState gstate (TheoryC name clist)  = theory  gstate name clist
updateState gstate (MappingC name vlist) = renList gstate name vlist
updateState gstate (ModExprC name mexps) = modExpr gstate name mexps

theory :: GraphState -> Name -> [Abs.Constr] -> GraphState
theory gs thryName cList =
  GraphState  
   (TGraph (Map.insert (getName thryName) newThry $ graphNodes gs) (graphEdges gs))
   (renames gs) 
  where newThry  = (GTheory NoParams $ flds cList)
        flds [] = NoFields
        flds ls = Fields ls              

renList :: GraphState -> Name -> [ViewPair] -> GraphState 
renList gs name rens =
  GraphState (graph gs) $
    Map.insert (getName name) newMap (renames gs)
  where newMap =  Map.fromList $ map (\(ViewPair x y) -> (getName x,getName y)) rens  

modExpr :: GraphState -> Name -> Abs.ModExpr -> GraphState
modExpr gs name mexpr =
  case mexpr of
    Extend srcName clist ->
      GraphState (updateGraph (graph gs) (getName name) $ Left $ computeExtend clist (srcThry srcName))
        (renames gs)
    Rename srcName rlist ->   
      GraphState
        (updateGraph (graph gs) (getName name) $ Left $ computeRename (rensToMapping rlist) (srcThry srcName))
        (renames gs)
    CombineOver trgt1 ren1 trgt2 ren2 srcName ->
     let gr = graph gs 
         p1 = getPath gr (srcThry srcName) (lookupName (getName trgt1) gr)
         p2 = getPath gr (srcThry srcName) (lookupName (getName trgt2) gr)
         qpath1 = QPath p1 $ rensToMapping ren1
         qpath2 = QPath p2 $ rensToMapping ren2
     in GraphState
        (updateGraph gr (getName name) $ Right $ computeCombine qpath1 qpath2)
        (renames gs)  
    Combine trgt1 trgt2 ->
      modExpr gs name $
        Abs.CombineOver trgt1 NoRens trgt2 NoRens (Name ((0,0),"Carrier"))
          -- TODO: (computeCommonSource name1 name2)
    Transport mapins srcName ->
     let getMappings = (renames gs) Map.! (getName mapins)
     in 
      GraphState
        (updateGraph (graph gs) (getName name) $ Left $ computeTransport getMappings $ srcThry srcName)
        (renames gs) 
  where
   srcThry n = lookupName (getName n) (graph gs) 
 
{-
createGraph :: [Abs.ModExpr] -> TGraph
createGraph mexprs =
  foldl createGraph' (TGraph Map.empty Map.empty) mexprs
-}
{- ------------------------------------------------------------- -} 
{-
data GraphState = GraphState TGraph (Map Name_ Mapping)

createGraph' :: GraphState -> Abs.ModExpr -> GraphState 
createGraph' (GraphState graph mappins) (Abs.Theory thryName cList) =
  GraphState newGraph mappins
  where newGraph =
 
createGraph' (GraphState graph mapins) (Abs.Combinator newName body) =
  case body of
    (Abs.MEName name) -> 
    (Abs.MERens renames) -> GraphState graph $ mapins newNames $ rensToMapping renames
    (Abs.Extend srcName cList) ->
      updateGraph graph (getName newName) $ Left (computeExtend cList srcThry) 
      where srcThry = lookupName (getName srcName) graph
    (Abs.Rename srcName renList) ->      
      updateGraph graph (getName newName) $ Left (computeRename (rens renList) srcThry)
      where srcThry = lookupName  (getName srcName) graph
    (Abs.CombineOver trgt1 ren1 trgt2 ren2 srcName) -> 
      updateGraph graph (getName newName) $ Right (computeCombine qpath1 qpath2)
      where
        srcThry = lookupName (getName srcName) graph
        p1 = getPath graph srcThry (lookupName (getName trgt1) graph)
        p2 = getPath graph srcThry (lookupName (getName trgt2) graph)
        qpath1 = QPath p1 $ rens ren1
        qpath2 = QPath p2 $ rens ren2
    (Abs.Combine name1 name2) ->
      createGraph' graph $
        Abs.Combinator newName $ Abs.CombineOver name1 NoRens name2 NoRens (Name ((0,0),"Carrier"))
          -- (computeCommonSource name1 name2)
    (Abs.Transport renMap srcName) ->
        updateGraph graph (getName newName) $ Left (computeTransport (rensM renMap) srcThry)
        where srcThry = lookupName (getName srcName) graph

{- ------------------ Computing with State ------------------------ -}

              
        
--computeCommonSource :: GTheory -> GTheory -> GTheory
--computeCommonSource d1 d2 =
      
        
-}  
rensToMapping :: Rens -> Mapping
rensToMapping NoRens = Map.empty
rensToMapping (Rens rlist) = Map.fromList $ map (\(RenPair x y) -> (getName x,getName y)) rlist

{- ------------------------------------------------------------- -} 

theoryToRecord :: Name_ -> GTheory -> Decl 
theoryToRecord thryName (GTheory ps fs) =
  Record (Name (noSrcLoc,thryName)) ps
         (RecordDeclDef (Name (noSrcLoc,"Set")) (Name (noSrcLoc,thryName++"C")) fs)  

recordToModule :: Name_ -> Decl -> Decl
recordToModule thryName record =
  Module_ $ Module (Name (noSrcLoc,thryName)) NoParams $ Decl_ [record] 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module (Name (noSrcLoc,moduleName)) NoParams $ 
       Decl_ (Map.elems $ modules) 

getLibDecls :: Abs.Module -> [Abs.Language]
getLibDecls (Abs.Module _ _ (Abs.Lang_ ls)) = ls
getLibDecls _ = error "No Modular expressions" 



{- -------------- building the theory graph -------------- -} 
{-
pmgraph :: TGraph 
pmgraph =  
  def "AddPM"    (Combine "AdditiveMagma" [] "Pointed0" [] "Carrier") $ 
  def "Pointed0" (Rename "Pointed" [("A","Nat"),("e","zero")]) $
  def "AdditiveMagma" (Rename "Magma" [("A","Nat"),("op","plus")]) $ 
  -- def "PointedMagma"  (Combine "Magma" [] "Pointed" [] "Carrier") $
  def "Magma"   (Extend "Carrier" ["op : A -> A -> A"]) $ 
  def "Pointed" (Extend "Carrier" ["e  : A"]) $
  def "Carrier" (Extend "Empty"   ["A  : Set"]) initGraph

emptyThry :: Theory 
emptyThry = Theory NoParams NoFields

initGraph :: TGraph
initGraph = TGraph (Map.singleton "Empty" emptyThry) (Map.empty) 

-}
{- ------------------ Printing ---------------------- -} 
{-
-- import           Tog.Abstract(Module,morePretty)   
-- import qualified Tog.PrettyPrint as PP

scopeCheckGraph :: TGraph -> Either PP.Doc Abs.Module
scopeCheckGraph tgraph = scopeCheckModule $ createModules $ nodes tgraph  
  
printToFile :: FilePath -> TGraph -> IO () 
printToFile filePath graph =
  writeFile filePath $ show $ printModule $ graph 

printModule :: TGraph -> PP.Doc 
printModule graph =
  case scopeCheckGraph graph of
     Left  err  -> err -- error "Invalid Graph"
     Right mods -> morePretty mods
-} 
