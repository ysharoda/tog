module Tog.Deriving.Main where

import           Tog.Raw.Abs 
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Hom
import           Tog.Deriving.TermLang
import           Tog.Deriving.TGraphTest 
import           Tog.Deriving.ProductTheory
import           Tog.Deriving.Signature 
import           Tog.Deriving.TypeConversions

import Tog.Parse

processDefs :: [Language] -> Module
processDefs = processModule . defsToModule

defsToModule :: [Language] -> Module
defsToModule = createModules . graphNodes . computeGraph

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
   Module n p $ Decl_ $ prodType : map genEverything decls   
processModule _ = error $ "Unparsed theory expressions exists" 

leverageThry :: Eq.EqTheory -> [Decl]
leverageThry thry =
 let hom = (homThryToDecl . homomorphism) thry
     trmlang = (termLangToDecl . termLang) thry
     prodthry = (prodTheoryToDecl . productThry) thry
     sigs = (sigToDecl . signature_) thry  
 in [hom,trmlang,prodthry,sigs]    

genEverything :: InnerModule -> InnerModule
genEverything m@(Module_ (Module n p (Decl_ decls))) =
  Module_ (Module n p (Decl_ $ decls ++ (concatMap leverageThry $ getEqTheories m)))
genEverything x = x  

{- ------- Filtering the EqTheories ------------ -} 

type InnerModule = Decl

getEqTheories :: InnerModule -> [Eq.EqTheory]
getEqTheories (Module_ (Module _ _ (Decl_ decls))) =
  map recordToEqTheory $ 
    filter (not . isEmptyTheory) $ concatMap declRecords decls
getEqTheories x = map recordToEqTheory $ declRecords x

declRecords :: Decl -> [TRecord]
declRecords (Record n p r) = [TRecord n p r]
declRecords (Module_ (Module _ _ (Decl_ decls))) = concatMap declRecords decls 
declRecords _ = []

isEmptyTheory :: TRecord -> Bool 
isEmptyTheory (TRecord _ NoParams (RecordDecl _)) = True
isEmptyTheory (TRecord _ NoParams (RecordDef  _ NoFields)) = True
isEmptyTheory (TRecord _ NoParams (RecordDeclDef _ _ NoFields)) = True
isEmptyTheory _ = False

{- ----------------- Testing ---------------------- -} 
test :: FilePath -> IO Module 
test file =
  do s <- readFile file
     case (parseModule s) of
       Right (Module _ _ (Lang_ defs)) ->
        do putStrLn "Generating Hom"
           return $ processDefs defs
       Right _ -> error "Invalid declaration"
       Left _ -> error "Cannot create modules"     

