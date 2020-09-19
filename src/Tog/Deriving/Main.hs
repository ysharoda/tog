module Tog.Deriving.Main
  ( processDefs
  , declRecords 
  ) where

import qualified Data.Map              as Map
import           Control.Lens (view)

import           Tog.Raw.Abs           as Abs
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Hom
import           Tog.Deriving.TGraphTest 
import           Tog.Deriving.ProductTheory
import           Tog.Deriving.Signature 
import           Tog.Deriving.TypeConversions
import           Tog.Deriving.Types
import           Tog.Deriving.TUtils  (mkName, setType,strToDecl, constrToBinding)
import           Tog.Deriving.RelationalInterp
import           Tog.Deriving.Terms
import           Tog.Deriving.Evaluator
import           Tog.Deriving.TogPrelude (prelude)
import           Tog.Deriving.Simplifier
import           Tog.Deriving.Induction 
import           Tog.Deriving.StagedTerms
import           Tog.Deriving.Tagless
import           Tog.Exporting.Agda
import Text.PrettyPrint.Leijen

processDefs :: [Language] -> Module
processDefs = processModule . defsToModule

defsToModule :: [Language] -> Module
defsToModule = createModules . view (graph . nodes) . computeGraph

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
   Module n p $ Decl_ $
     -- (prodType : map strToDecl prelude) ++ 
      prodType : map genEverything decls   
processModule _ = error "Unparsed theory expressions exists" 

leverageThry :: Eq.EqTheory -> [Decl]
leverageThry thry =
 let sigs = (sigToDecl . signature_) thry
     prodthry = (prodTheoryToDecl . productThry) thry
     hom = homomorphism thry
     relInterp = relationalInterp thry
          {-
     trmLangs = termLangs thry
     temLangsDecls = termLangsToDecls trmLangs
     simplifiers = simplifyFuncs thry trmLangs
     evaluators = evalFuncs thry trmLangs
     inductions = inductionFuncs trmLangs
     stagedTLs = stagedFuncs trmLangs
     tagless = taglessRep thry  -}
 in [sigs, prodthry, hom, relInterp] -- ++ temLangsDecls 
   -- ++ simplifiers ++ evaluators ++ inductions ++ stagedTLs ++ [tagless] 
    
    --[trmlang, openTrmLang] ++ evalTrmLang ++ evalOpenTrmLang ++ simplifier ++
    --stagedClosedTerms ++ stagedOpenTerms ++ [tagless] 

genEverything :: InnerModule -> InnerModule
genEverything m@(Module_ (Module n p (Decl_ decls))) =
  Module_ $ Module n p (Decl_ $ decls ++ (concatMap leverageThry $ getEqTheories m)) 
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
theoryToRecord n (GTheory ds wst) =
  Record (mkName n) prms (RecordDeclDef setType (mkName $ n++"C") fields)
  where prms = if wst == 0 || null ds then NoParams else ParamDecl $ map constrToBinding (take wst ds)
        fields = let flds = (drop wst ds) in if null flds then NoFields else Fields flds 

recordToModule :: Name_ -> Decl -> Decl
recordToModule n record =
  Module_ $ Module (mkName n) NoParams $ Decl_ [record] 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module mathscheme NoParams $ Decl_ $ Map.elems modules 


