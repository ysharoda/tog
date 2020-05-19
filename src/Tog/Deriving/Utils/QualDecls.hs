-- P : Parameter
-- PConstr: a Constr has a boolean value indicating if it is a parameter or not
module Tog.Deriving.Utils.QualDecls where 

import Control.Lens

import Tog.Raw.Abs   
import Tog.Deriving.Types  (Name_)
import Tog.Deriving.TUtils (createId, mkArg)
import Tog.Deriving.EqTheory
import Tog.Deriving.Lenses   (name)
  
data PConstr = PConstr {
  pname :: Name_,
  ptype  :: Expr ,
  isParam :: Bool
}

mkPConstr :: Constr -> Int -> Int -> PConstr
mkPConstr (Constr nm ctyp) wst indx =
  PConstr (nm ^. name) ctyp (indx < wst)

mkPConstrs :: EqTheory -> (PConstr,[PConstr],[PConstr])
mkPConstrs t =
  let wst = t ^. waist
      axms  = t ^. axioms
      funcs = t ^. funcTypes
      constrs = (t ^. sort) : (funcs ++ axms)
      pconstrs = map (\(c,i) -> mkPConstr c wst i) $ zip  constrs [0..length constrs]
   in (head pconstrs,
       take (length funcs) (drop 1 pconstrs),
       take (length axms)  (drop (1 + length funcs) pconstrs)) 

-- If the constr is a param, qualify it with an index, (like A1 and A2) 
-- If not, qualify with the instance name  (like (op M1)) 
mkPExpr :: PConstr -> (Name_,Int) -> Expr 
mkPExpr (PConstr nm _ True) (_,indx) = createId (nm ++ show indx)
mkPExpr (PConstr nm _ False) (instNm,_) = App [mkArg nm, mkArg instNm] 

