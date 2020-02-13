module Tog.TGraphTest where

import qualified Data.Map        as Map

import           Tog.TGraph      as TGraph
import           Tog.Raw.Abs     as Abs

getName :: Name -> String
getName (Name (_,str)) = str 

createGraph :: [Abs.ModExpr] -> TGraph
createGraph mexprs =
  foldl createGraph' (TGraph Map.empty Map.empty) mexprs

createGraph' :: TGraph -> Abs.ModExpr -> TGraph 
createGraph' graph (Abs.Theory thryName cList) =
  TGraph (Map.insert (getName thryName) (GTheory NoParams $ flds cList) $nodes graph)
         (edges graph)
  where flds [] = NoFields
        flds ls = Fields ls 
createGraph' graph (Abs.Extend newThryName srcThryName cList) =
  updateGraph graph (getName newThryName) $ Left (computeExtend cList srcThry) 
  where srcThry = lookupName (getName srcThryName) graph 
createGraph' graph (Abs.Rename newThryName srcThryName renList) =
  updateGraph graph (getName newThryName) $ Left (computeRename (rens renList) srcThry)
  where srcThry = lookupName  (getName srcThryName) graph
createGraph' graph (Abs.Combine newThryName trgt1 ren1 trgt2 ren2 srcThryName) =
  updateGraph graph (getName newThryName) $ Right (computeCombine qpath1 qpath2)
  where srcThry = lookupName (getName srcThryName) graph
        p1 = getPath graph srcThry (lookupName (getName trgt1) graph)
        p2 = getPath graph srcThry (lookupName (getName trgt2) graph)
        qpath1 = QPath p1 $ rens ren1
        qpath2 = QPath p2 $ rens ren2
                                      
rens :: Rens -> Mapping
rens NoRens = Map.empty
rens (Rens rlist) = Map.fromList $ map (\(RenPair x y) -> (getName x,getName y)) rlist

theoryToRecord :: Name_ -> GTheory -> Decl 
theoryToRecord thryName (GTheory ps fs) =
  Record (Name (noSrcLoc,thryName)) ps
         (RecordDeclDef (Name (noSrcLoc,"Set")) (Name (noSrcLoc,thryName++"C")) fs)  

recordToModule :: Name_ -> Decl -> Decl
recordToModule thryName record =
  Module_ $ Module (Name (noSrcLoc,thryName)) NoParams $ DeclC [record] 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module (Name (noSrcLoc,"MathScheme")) NoParams $ 
       DeclC (Map.elems $ modules) 

getModExprs :: Abs.Module -> [Abs.ModExpr]
getModExprs (Abs.Module _ _ (Abs.MExprC mexprs)) = mexprs


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
