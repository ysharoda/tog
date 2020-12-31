module Interpret.Deriving.Tagless where

import Tog.Raw.Abs
import Interpret.Deriving.EqTheory 
import Interpret.Utils.Functions
import Interpret.Utils.TUtils
import Interpret.Utils.Renames (foldren)
import Interpret.Utils.Lenses (name)

import Control.Lens ((^.))
import Data.Map as Map (Map,fromList,toList) 

taglessName :: Name_
taglessName = "StagedRepr"

reprTypeName :: String 
reprTypeName = "Repr"

mapping :: EqTheory -> Map Name_ Name_
mapping eq =
  let names = map (\(Constr n _) -> n ^. name) (eq ^. funcTypes) 
  in Map.fromList (zip names (map (++ "T") names)) 

taglessRep :: EqTheory -> Decl 
taglessRep eq =
 let carrierNm = getConstrName (eq ^. sort)
     fdecls = foldren eq (Map.toList $ mapping eq) ^. funcTypes
 in Record (mkName $ taglessName)
  (ParamDecl [Bind [mkArg carrierNm] setTypeAsId,
              Bind [mkArg reprTypeName] $ Fun (App [mkArg "Set"]) (App [mkArg "Set"])]) $ 
  RecordDeclDef setType (mkName "repr") $
   Fields $ map (liftConstr reprTypeName) fdecls

