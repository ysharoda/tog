module Tog.TGraphTest where

import qualified Data.Map        as Map

import Tog.TGraph
import           Tog.Raw.Abs     as Abs
import qualified Tog.PrettyPrint as PP
import           Tog.ScopeCheck
import           Tog.Abstract(Module,morePretty)    

run :: TGraph -> IO ()  
run graph =
  let checkOutput (Left err)   = err
      checkOutput (Right mods) = morePretty mods 
  in putStrLn $ unlines $ map (show . checkOutput) $ typeCheck graph  

typeCheck :: TGraph -> [Either PP.Doc Tog.Abstract.Module]
typeCheck graph =
  let thrs = nodes graph
      records = Map.elems $ Map.mapWithKey theoriesToRecords thrs
  in map (scopeCheckModule . createModule) records 

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

{-
carrier = def "Carrier" (Extend "Empty"   ["A  : Set"]) initGraph
pointed = def "Pointed" (Extend "Carrier" ["e : A"]) carrier
magma   = def "Magma"   (Extend "Carrier" ["op : A -> A -> A"]) pointed
pointedMagma = def "PointedMagma"  (Combine "Magma" [] "Pointed" [] "Carrier") magma
additiveMagma = def "AdditiveMagma" (Rename "Magma" [("A","Nat"),("op","+")]) pointedMagma
pointed0 = def "Pointed0" (Rename "Pointed" [("A","Nat"),("e","0")]) additiveMagma
addpm =   def "AddPM"    (Combine "AdditiveMagma" [] "Pointed0" [] "Carrier") pointed0 
-}

emptyThry :: Theory 
emptyThry = Theory NoParams NoFields

initGraph :: TGraph
initGraph = TGraph (Map.singleton "Empty" emptyThry) (Map.empty) 



  
