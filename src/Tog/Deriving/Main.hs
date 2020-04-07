module Tog.Deriving.Main
  ( processDefs
  ) where

import qualified Data.Map              as Map
import           Control.Lens (view)

import           Tog.Raw.Abs           as Abs
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Hom
import           Tog.Deriving.TermLang
import           Tog.Deriving.TGraphTest 
import           Tog.Deriving.ProductTheory
import           Tog.Deriving.Signature 
import           Tog.Deriving.TypeConversions
import           Tog.Deriving.Types
import           Tog.Deriving.TUtils  (mkName, setType)

processDefs :: [Language] -> Module
processDefs = processModule . defsToModule

defsToModule :: [Language] -> Module
defsToModule = createModules . view (graph . nodes) . computeGraph

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
   Module n p $ Decl_ $ prodType : map genEverything decls   
processModule _ = error $ "Unparsed theory expressions exists" 

leverageThry :: Eq.EqTheory -> [Decl]
leverageThry thry =
 let hom = (homThryToDecl . homomorphism) thry
     trmlang = termLang thry
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

{- ------------------------------------------------------------- -} 

mathscheme :: Name
mathscheme = mkName "MathScheme" 

theoryToRecord :: Name_ -> GTheory -> Decl 
theoryToRecord n (GTheory ps fs) =
  Record (mkName n) ps (RecordDeclDef setType (mkName $ n++"C") fs)  

recordToModule :: Name_ -> Decl -> Decl
recordToModule n record =
  Module_ $ Module (mkName n) NoParams $ Decl_ [record] 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module mathscheme NoParams $ Decl_ $ Map.elems modules 
