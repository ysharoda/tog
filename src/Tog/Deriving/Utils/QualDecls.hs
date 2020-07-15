-- P : Parameter
-- PConstr: a Constr has a boolean value indicating if it is a parameter or not
module Tog.Deriving.Utils.QualDecls where 

import Control.Lens

import Tog.Raw.Abs   
import Tog.Deriving.Types  (Name_)
import Tog.Deriving.TUtils (createId, mkArg)
--import Tog.Deriving.EqTheory
import Tog.Deriving.Lenses   (name)
  
data PConstr = PConstr {
  pname :: Name_,
  ptype  :: Expr ,
  isParam :: Bool
}

mkPConstr :: Constr -> Int -> Int -> PConstr
mkPConstr (Constr nm ctyp) wst indx =
  PConstr (nm ^. name) ctyp (indx < wst)

-- If the constr is a param, qualify it with an index, (like A1 and A2) 
-- If not, qualify with the instance name  (like (op M1)) 
mkPExpr :: PConstr -> (Name_,Int) -> Expr 
mkPExpr (PConstr nm _ True) (_,indx) =
  if indx /= 0 then createId (nm ++ show indx)
  else createId nm 
mkPExpr (PConstr nm _ False) (instNm,_) = App [mkArg nm, mkArg instNm] 

