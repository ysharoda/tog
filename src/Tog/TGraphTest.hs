module TGraphTest where

import qualified Data.Map        as Map

import Tog.TGraph
import           Tog.Raw.Abs     as Abs
import qualified Tog.PrettyPrint as PP
import           Tog.ScopeCheck
import           Tog.Abstract(Module)


typeCheck :: TGraph -> [Either PP.Doc Tog.Abstract.Module]
typeCheck graph =
  let thrs = nodes graph
      records = Map.elems $ Map.mapWithKey theoriesToRecords thrs
  in  map (scopeCheckModule . createModule) records 

theoriesToRecords :: Name_ -> Theory -> Decl 
theoriesToRecords thryName (Theory ps fs) =
  Record (Name (noSrcLoc,thryName)) ps
         (RecordDeclDef (Name (noSrcLoc,"Set")) (Name (noSrcLoc,thryName++"C")) fs)  

createModule :: Decl -> Abs.Module
createModule record = 
  Module (Name (noSrcLoc,"MathScheme")) NoParams [record] 

{- -------------- building the theory graph -------------- -} 

pmgraph :: TGraph 
pmgraph =
  def "AddPM"    (Combine "AdditiveMagma" [] "Pointed0" [] "Carrier") $ 
  def "Pointed0" (Rename "Pointed" [("A","Nat"),("e","0")]) $
  def "AdditiveMagma" (Rename "Magma" [("A","Nat"),("op","+")]) $ 
  def "PointedMagma"  (Combine "Magma" [] "Pointed" [] "Carrier") $
  def "Magma"   (Extend "Carrier" ["op : A -> A -> A"]) $ 
  def "Pointed" (Extend "Carrier" ["e  : A"]) $
  def "Carrier" (Extend "Empty"   ["A  : Set"]) initGraph

emptyThry :: Theory 
emptyThry = Theory NoParams NoFields

initGraph :: TGraph
initGraph = TGraph (Map.singleton "Empty" emptyThry) (Map.empty) 

  
