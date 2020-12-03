module Tog.Deriving.Tagless where

import Tog.Raw.Abs
import Tog.Deriving.EqTheory 
import Tog.Deriving.Utils.Functions
import Tog.Deriving.Types  (Name_)
import Tog.Deriving.TUtils
import Tog.Deriving.Utils.Renames (foldren)
import Data.Map as Map (Map,fromList,toList) 
import Tog.Deriving.Lenses (name)
import Control.Lens ((^.))

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

