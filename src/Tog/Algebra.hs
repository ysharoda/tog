module Tog.Algebra where

import Tog.Raw.Abs 
import Tog.TypeConversions
import Tog.EqTheory
import Tog.Hom
import Tog.TermLang 
--import qualified Data.Generics as Generics

import Tog.Parse
import Tog.TGraphTest 

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
  Module n p $ Decl_ $ map createTermLang decls   
processModule _ = error $ "Unparsed theory expressions exists" 
--processModule_ decls =   Generics.everything (++) (Generics.mkQ [] (\(Module_ m) -> [m])) decls

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


{-
eqNames :: Name -> Name -> Bool 
eqNames (Name (_,n1)) (Name (_,n2)) = n1 == n2 

-- in case the module has more than one record, we choose the record with the same name as the inner module 
recordWithName :: Name -> [Decl] -> TRecord
recordWithName name ((Record n p r):ds) =
  if eqNames n name then (TRecord n p r) else recordWithName ds name
recordWithName name ((Module_ (Module n p (Decl_ decls))):ds) =
  let r = map (recordWithName name) decls
  in if r == [] then recordWithName ds
     else if length r == 1 then head r
     else error "Multiple records with the same name"
recordWithName name (_:ds) = recordWithName name ds           
-}


{-
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
