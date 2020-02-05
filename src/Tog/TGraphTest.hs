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
  in putStrLn $ show $ checkOutput $ scopeCheck graph  

{-
typeCheck :: TGraph -> Either PP.Doc Tog.AbstractModule
typeCheck graph = do
  mbErr <- runExceptT $ do
    exceptShowErr "Scope" $ scopeCheck graph 
-}
scopeCheck :: TGraph -> Either PP.Doc Tog.Abstract.Module
scopeCheck graph =
  scopeCheckModule $ createModules $ nodes graph 

theoryToRecord :: Name_ -> Theory -> Decl 
theoryToRecord thryName (Theory ps fs) =
  Record (Name (noSrcLoc,thryName)) ps
         (RecordDeclDef (Name (noSrcLoc,"Set")) (Name (noSrcLoc,thryName++"C")) fs)  

recordToModule :: Int -> Decl -> Decl
recordToModule num record =
  Module_ $ Module (Name (noSrcLoc,"MathScheme"++show num)) NoParams [record] 

createModules :: Map.Map Name_ Theory -> Abs.Module
createModules theories =
  let records = Map.elems $ Map.mapWithKey theoryToRecord theories
      numRecPair = Map.fromList $ zip [1..length theories] records
  in Module (Name (noSrcLoc,"MathScheme")) NoParams $ 
       Map.elems $ Map.mapWithKey recordToModule numRecPair 


{- -------------- building the theory graph -------------- -} 

pmgraph :: TGraph 
pmgraph =  
  def "AddPM"    (Combine "AdditiveMagma" [] "Pointed0" [] "Carrier") $ 
  def "Pointed0" (Rename "Pointed" [("A","Nat"),("e","zero")]) $
  def "AdditiveMagma" (Rename "Magma" [("A","Nat"),("op","plus")]) $ 
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



  
