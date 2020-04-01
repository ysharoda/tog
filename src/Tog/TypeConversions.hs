module Tog.TypeConversions where

import qualified Tog.EqTheory as Eq
import Tog.Hom 
import Tog.Raw.Abs       as Abs
import Tog.TUtils 
import Tog.Utils 

data TRecord = TRecord Name Params RecordBody deriving (Show,Eq) 

recordToEqTheory :: TRecord -> Eq.EqTheory
recordToEqTheory record@(TRecord name params _) =
  Eq.EqTheory (getNameAsStr name) 
   (getRecordSort record)
   (getRecordComps isFunc record)
   (getRecordComps isAxiom record)
   (paramsNum params)

getRecordSort :: TRecord -> Constr
getRecordSort record =
  let sort = getRecordComps isSort record
  in if (sort == [])
     then error $ "Cannot determine the sort"
     else if (length sort > 1)
     then error $ "Theory has more than one sort"
     else head sort 

getRecordComps :: (Expr -> Bool) -> TRecord -> [Constr]
getRecordComps p (TRecord _ params body) =
 let par = checkParam p params
     con = filter (p . getExpr) $ getRecordConstrs body
 in (paramToConstr par) ++ con

homThryToDecl :: HomThry -> Decl
homThryToDecl (HomThry name hargs eargs func axioms) =
  Record (mkName name)
   (mkParams $ hargs ++ eargs)
   (RecordDeclDef setType (mkConstructor name) (mkFields $ func : axioms))      

{- ----------- Helper Functions --------------- -}

mkParams :: [Binding] -> Params
mkParams [] = NoParams
mkParams ls = ParamDecl ls    

mkFields :: [Constr] -> Fields
mkFields [] = NoFields
mkFields ls = Fields ls    
   
paramToConstr :: Abs.Params -> [Constr] 
paramToConstr NoParams = []
paramToConstr (ParamDecl binds) = concatMap bindingToConstr binds
paramToConstr (ParamDef _) = []    
      
bindingToConstr :: Abs.Binding -> [Constr]
bindingToConstr bind =
  let names = concatMap getArgName $ getBindingArgs bind
      typ = getBindingExpr bind
  in map (\n -> Constr (Name (noSrcLoc,n)) typ) names  

getRecordConstrs :: Abs.RecordBody -> [Constr]
getRecordConstrs (RecordDef _ fields) = getFieldConstrs fields 
getRecordConstrs (RecordDeclDef _ _ fields) = getFieldConstrs fields
getRecordConstrs _ = []

getFieldConstrs :: Abs.Fields -> [Constr]
getFieldConstrs NoFields = []
getFieldConstrs (Fields cs) = cs 

paramsNum :: Abs.Params -> Int
paramsNum NoParams = 0
paramsNum (ParamDecl ls) = length $ concatMap getBindingArgs ls 
paramsNum (ParamDef ls) = length ls 
