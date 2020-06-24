module Tog.Deriving.TypeConversions
  ( recordToEqTheory
  , TRecord (TRecord)
  ) where

import           Control.Lens ((^.), view)

import Tog.Deriving.PConstr 
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name, cExpr)
import           Tog.Deriving.TUtils 
import           Tog.Deriving.Utils 
import           Tog.Raw.Abs           as Abs

data TRecord = TRecord Name Params RecordBody

recordToEqTheory :: TRecord -> Eq.EqTheory
recordToEqTheory record@(TRecord nm params _) =
  Eq.build (nm^.name) 
   (getRecordSort record)
   (getRecordComps isFunc record)
   (getRecordComps isAxiom record) 

getRecordSort :: TRecord -> Eq.PConstr
getRecordSort record =
  let sort = getRecordComps isSort record
  in if (sort == [])
     then error $ "Cannot determine the sort"
     else if (length sort > 1)
     then error $ "Theory has more than one sort"
     else head sort

getRecordComps :: (Expr -> Bool) -> TRecord -> [Eq.PConstr]
getRecordComps p (TRecord _ params body) =
 let par = checkParam p params
     con = filter (p . getExpr) $ getRecordPConstrs body
 in (paramToPConstr par) ++ con

{- ----------- Helper Functions --------------- -}

paramToPConstr :: Abs.Params -> [Eq.PConstr] 
paramToPConstr NoParams = []
paramToPConstr (ParamDecl binds) = concatMap bindingToPConstr binds
paramToPConstr (ParamDef _) = []    
      
bindingToPConstr :: Abs.Binding -> [Eq.PConstr]
bindingToPConstr bind =
  let names = map getArgName $ getBindingArgs bind
      typ = getBindingExpr bind
  in map (\n -> Eq.pconstr n typ True) names  

getRecordPConstrs :: Abs.RecordBody -> [Eq.PConstr]
getRecordPConstrs (RecordDef _ fields) =
  let flds = getFields fields
  in map (\(Constr n p) -> (Eq.pconstr (n ^. name) p False)) flds 
getRecordPConstrs (RecordDeclDef _ _ fields) =
  let flds = getFields fields
  in map (\(Constr n p) -> (Eq.pconstr (n ^. name) p False)) flds 
getRecordPConstrs _ = []

paramsNum :: Abs.Params -> Int
paramsNum NoParams = 0
paramsNum (ParamDecl ls) = length $ concatMap getBindingArgs ls 
paramsNum (ParamDef ls) = length ls 
