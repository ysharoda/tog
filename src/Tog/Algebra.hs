module Tog.Algebra where

import Tog.Raw.Abs 
import Tog.TypeConversions
import Tog.EqTheory
import Tog.Hom
import Tog.TermLang
import Tog.ProductTheory
import Tog.Signature 
--import qualified Data.Generics as Generics

import Tog.Parse
import Tog.TGraphTest 

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
   Module n p $ Decl_ $ genProdType : map genEverything decls   
processModule _ = error $ "Unparsed theory expressions exists" 
--processModule_ decls =   Generics.everything (++) (Generics.mkQ [] (\(Module_ m) -> [m])) decls

leverageThry :: EqTheory -> [Decl]
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

getEqTheories :: InnerModule -> [EqTheory]
getEqTheories (Module_ (Module _ _ (Decl_ decls))) =
  let records = filter (\r -> not $ isEmptyTheory r) $ concatMap declRecords decls
  in map recordToEqTheory records 
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
           return $ processModule $ createModules $ graphNodes $ computeGraphState defs
       Right _ -> error "Invalid declaration"
       Left _ -> error "Cannot create modules"     
           -- $ show $ length $ readModRecs mod -- $ Module n p $ readModuleRecords decls -- (decls ++ (map createHom $ readRecords decls)) 


-- Generics.everything (++) (Generics.mkQ [] (\(Record n p r) -> [TRecord n p r])) md


{-

getRecords :: Module -> [TRecord] 
getRecords (Module _ _ (Decl_ mdecls)) = concatMap records mdecls 
 where records (Record n p r) = [TRecord n p r]
       records (Module_ (Module _ _ (Decl_ decls))) = concatMap records decls 
       records _ = [] 



processModule_ mod =
 let records = readInnerModuleRecords mod
     homs = map homomorphism $ map recordToEqTheory records
 in appendToModule_ mod $ map homThryToDecl homs 
-}
{-
declRecords :: Decl -> [TRecord]
declRecords (Record n p r) = [TRecord n p r]
declRecords _ = [] 
-}

--testSyb :: Module -> [Record]
{-
testSyb decl = 
  Generics.everything (++) (Generics.mkQ [] (\(Id n) -> [n])) decl


-- needed for testing 
recordToDecl :: [TRecord] -> [Decl]
recordToDecl rls = map (\(TRecord n p r) -> (Record n p r)) rls 

readModuleRecords :: Module -> [TRecord]
readModuleRecords (Module _ _ (Decl_ decls)) =
  concatMap declRecords decls



readInnerModuleRecords :: InnerModule -> [TRecord]   
readInnerModuleRecords (Module_ mod) =
  readModuleRecords mod
readInnerModuleRecords _ = error "not a module"  
-}

{-
{- ------- Creating Homomorphisms ------------ -} 

createHomThry :: InnerModule -> InnerModule
createHomThry m@(Module_ (Module n p (Decl_ decls))) =
  let hom = map (homThryToDecl . homomorphism) $ getEqTheories m
  in Module_ $ Module n p $ Decl_ (decls ++ hom)
createHomThry _ = error $ "record not contained in an inner module"

isEmptyTheory :: TRecord -> Bool 
isEmptyTheory (TRecord _ NoParams (RecordDecl _)) = True
isEmptyTheory (TRecord _ NoParams (RecordDef  _ NoFields)) = True
isEmptyTheory (TRecord _ NoParams (RecordDeclDef _ _ NoFields)) = True
isEmptyTheory _ = False

{- -------- Creating Term Language -------------- -}

createTermLang :: InnerModule -> InnerModule
createTermLang m@(Module_ (Module n p (Decl_ decls))) =
  let thrs = getEqTheories m
      filterTh = filter (\t -> not $ getThryName t == "Carrier" || getThryName t == "Empty") thrs 
      lang = map (termLangToDecl . termLang) $ filterTh-- getEqTheories filterTh
  in Module_ $ Module n p $ Decl_ (decls ++ lang) 
createTermLang _ = error $ "record not contained in an inner module"

{- ---------- Creating Product Algebras ----------- -}
createProdAlgebra :: InnerModule -> InnerModule
createProdAlgebra m@(Module_ (Module n p (Decl_ decls))) =
  let thrs = getEqTheories m
      filterTh = filter (\t -> not $ getThryName t == "Carrier" || getThryName t == "Empty") thrs 
      prod = map (prodTheoryToDecl . productThry) $ filterTh-- getEqTheories filterTh
  in Module_ $ Module n p $ Decl_ (decls ++ prod) 
createProdAlgebra _ = error $ "record not contained in an inner module"
-} 
