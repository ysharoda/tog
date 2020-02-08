module Tog.TGraphTest where

import qualified Data.Map        as Map

import Tog.TGraph
import           Tog.Raw.Abs     as Abs
import qualified Tog.PrettyPrint as PP
import           Tog.ScopeCheck(scopeCheckModule)
--import           Tog.CheckFile(checkModule,checkGraph) 
import           Tog.Abstract(Module,morePretty)   

printTGraph :: PP.Doc
printTGraph = printModule pmgraph 

printToFile :: FilePath -> TGraph -> IO () 
printToFile filePath graph =
  writeFile filePath $ show $ printModule $ graph 

printModule :: TGraph -> PP.Doc 
printModule graph =
  case scopeCheckGraph graph of
     Left  err  -> err -- error "Invalid Graph"
     Right mods -> morePretty mods
  
scopeCheckGraph :: TGraph -> Either PP.Doc Tog.Abstract.Module
scopeCheckGraph graph =
  scopeCheckModule $ createModules $ nodes graph 

theoryToRecord :: Name_ -> Theory -> Decl 
theoryToRecord thryName (Theory ps fs) =
  Record (Name (noSrcLoc,thryName)) ps
         (RecordDeclDef (Name (noSrcLoc,"Set")) (Name (noSrcLoc,thryName++"C")) fs)  

recordToModule :: Name_ -> Decl -> Decl
recordToModule thryName record =
  Module_ $ Module (Name (noSrcLoc,thryName)) NoParams [record] 

createModules :: Map.Map Name_ Theory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module (Name (noSrcLoc,"MathScheme")) NoParams $ 
       (Map.elems $ modules) 


{- -------------- building the theory graph -------------- -} 

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


{- ---------- Trying to call the type checker -------------- -}
{-
run :: TGraph -> IO ()  
run graph =
  let checkOutput (Left err)   = err
      checkOutput (Right mods) = morePretty mods 
  in putStrLn $ show $ checkOutput $ scopeCheckGraph graph  

-}
{-
run :: TGraph -> IO ()
run graph = do
  s <- initCheckState 
runTC sigEmpty ()  $ typeCheck graph 
-}
-- typeCheck :: TGraph -> Either PP.Doc Tog.AbstractModule
-- unsafePerformIO 
--typeCheck graphModule =
--  runTC 

-- typeCheck :: Tog.Abstract.Module -> IO PP.Doc
  
{-

  checkGraph graphModule
  return $ case doc of
    Left  d -> d
    Right _ -> error "cannot type check module" 


    let checkOutput (Left err)   = error "invalide module" 
             checkOutput (Right mods) = checkGraph mods -- (return ())
         in checkOutput (scopeCheckGraph graph)   


-}

-- type CheckM t = TC t (Env t) (CheckState t)
-- type CCheckM t = forall b. CheckM t b -> CheckM t b  
--  checkModule (scopeCheck graph) (return ()) 
{-  mbErr <- runExceptT $ do
    exceptShowErr "Scope" $ scopeCheck graph
  case mbErr of
    Left err -> Just err
    Right int -> checkFile int $ \sig mbErr' 
-}
