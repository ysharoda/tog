module Tog.Deriving.TypeConversions
  ( TRecord( TRecord )
  , homThryToDecl
  , recordToEqTheory
  ) where

import           Control.Lens ((^.), view)

import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Hom 
import           Tog.Deriving.Lenses   (name, cExpr)
import           Tog.Deriving.TUtils 
import           Tog.Deriving.Utils 
import           Tog.Raw.Abs           as Abs

data TRecord = TRecord Name Params RecordBody deriving (Show,Eq) 

recordToEqTheory :: TRecord -> Eq.EqTheory
recordToEqTheory record@(TRecord nm params _) =
  Eq.EqTheory (nm^.name) 
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
     con = filter (p . view cExpr) $ getRecordConstrs body
 in (paramToConstr par) ++ con

homThryToDecl :: HomThry -> Decl
homThryToDecl (HomThry nm hargs eargs fnc axioms) =
  Record (mkName nm)
   (mkParams $ hargs ++ eargs)
   (RecordDeclDef setType (mkName $ nm ++ "C") (mkField $ fnc : axioms))

{- ----------- Helper Functions --------------- -}

mkParams :: [Binding] -> Params
mkParams [] = NoParams
mkParams ls = ParamDecl ls    

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
