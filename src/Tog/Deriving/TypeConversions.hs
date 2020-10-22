module Tog.Deriving.TypeConversions
  ( recordToEqTheory
  , TRecord (TRecord)
  , getEqTheories
  , theoryToRecord
  , recordToModule
  ) where

import           Control.Lens ((^.), view)
import           Data.List ((\\)) 

import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name, cExpr)
import           Tog.Deriving.TUtils 
import           Tog.Deriving.Utils 
import           Tog.Raw.Abs           as Abs
import           Tog.Deriving.Types 

data TRecord = TRecord Name Params RecordBody deriving Show 

recordToEqTheory :: TRecord -> Eq.EqTheory
recordToEqTheory record@(TRecord nm params rbdy) =
  let sort = getRecordSort record
      fsyms = getRecordComps isFunc record
      axioms = (paramToConstr params ++ getRecordConstrs rbdy) \\ (sort : fsyms) 
  in Eq.build (nm^.name) 
       sort fsyms axioms 
       (paramsNum params)

{-
gTheoryToEqTheory :: Name_ -> GTheory -> Eq.EqTheory
gTheoryToEqTheory nm gtheories =
 Eq.build nm
    (getRecordComps isSort (gtheories) 
-}
getRecordSort :: TRecord -> Constr
getRecordSort record =
  let sort = getRecordComps isSort record
  in if (sort == [])
     then error $ show record -- "Cannot determine the sort"
     else if (length sort > 1)
     then error $ "Theory has more than one sort"
     else head sort 

getRecordComps :: (Expr -> Bool) -> TRecord -> [Constr]
getRecordComps p (TRecord _ params body) =
 let par = checkParam p params
     con = filter (p . view cExpr) $ getRecordConstrs body
 in (paramToConstr par) ++ con

{- ----------- Helper Functions --------------- -}

paramToConstr :: Abs.Params -> [Constr] 
paramToConstr NoParams = []
paramToConstr (ParamDecl binds) = concatMap bindingToConstr binds
paramToConstr (ParamDef _) = []    
      
bindingToConstr :: Abs.Binding -> [Constr]
bindingToConstr bind =
  let names = map getArgName $ getBindingArgs bind
      typ = getBindingExpr bind
  in map (\n -> Constr (mkName n) typ) names  

getRecordConstrs :: Abs.RecordBody -> [Constr]
getRecordConstrs (RecordDef _ fields) = getFields fields 
getRecordConstrs (RecordDeclDef _ _ fields) = getFields fields
getRecordConstrs _ = []

paramsNum :: Abs.Params -> Int
paramsNum NoParams = 0
paramsNum (ParamDecl ls) = length $ concatMap getBindingArgs ls 
paramsNum (ParamDef ls) = length ls 

theoryToRecord :: Name_ -> GTheory -> Decl 
theoryToRecord n (GTheory ds wst) =
  Record (mkName n) prms (RecordDeclDef setType (mkName $ n++"C") fields)
  where prms = if wst == 0 || null ds then NoParams else ParamDecl $ map constrToBinding (take wst ds)
        fields = let flds = (drop wst ds) in if null flds then NoFields else Fields flds
{- -- Tog does not allow opening records, only modules. 
openRecord :: Decl -> Decl
openRecord (Record nm _ _) = Abs.Open $ (Abs.NotQual nm)
openRecord decl = decl
-}

{- ------- Used in Main Module ------------ -} 

declRecords :: Decl -> [TRecord]
declRecords (Record n p r) = [TRecord n p r]
declRecords (Module_ (Module _ _ (Decl_ decls))) = concatMap declRecords decls 
declRecords _ = []

isEmptyTheory :: TRecord -> Bool 
isEmptyTheory (TRecord _ NoParams (RecordDecl _)) = True
isEmptyTheory (TRecord _ NoParams (RecordDef  _ NoFields)) = True
isEmptyTheory (TRecord _ NoParams (RecordDeclDef _ _ NoFields)) = True
isEmptyTheory _ = False


recordToModule :: Name_ -> Decl -> Decl
recordToModule n record =
  Module_ $ Module (mkName n) NoParams $ Decl_ [record] -- ,openRecord record] 

getEqTheories :: Decl -> [Eq.EqTheory]
getEqTheories (Module_ (Module nm _ (Decl_ decls))) =
  let trecordName (TRecord n _ _) = n 
  in map recordToEqTheory $ 
       filter (\tr -> (trecordName tr == nm) && (not . isEmptyTheory) tr) $ concatMap declRecords decls
getEqTheories x = map recordToEqTheory $ declRecords x
