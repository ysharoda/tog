{-# LANGUAGE TemplateHaskell #-}
-- P : Parameter
-- PEqTheory: every Constr has a boolean value indicating if it is a parameter or not (PConstr)
module Tog.Deriving.PEqTheory where 

import Control.Lens

import           Tog.Raw.Abs   
import           Tog.Deriving.Types  (Name_)
import           Tog.Deriving.TUtils (createId, mkArg)
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name)
  
data PConstr = PConstr {
  pname :: Name_,
  typ  :: Expr ,
  isParam :: Bool
}

data PEqTheory = PEqTheory {
  _thryName :: Name_ ,
  _sort :: PConstr,
  _funcTypes  :: [PConstr],
  _axioms     :: [PConstr]
  }

makeLenses ''PEqTheory   

constrToPConstr :: Constr -> Int -> Int -> PConstr
constrToPConstr (Constr nm ctyp) waist indx =
  PConstr (nm ^. name) ctyp (indx < waist) 

eqToPEqTheory :: Eq.EqTheory -> PEqTheory
eqToPEqTheory eqThry =
  let ftyps = eqThry ^. Eq.funcTypes
      axms  = eqThry ^. Eq.axioms
      constrs = (eqThry ^. Eq.sort) : (ftyps ++ axms)
      wst = (eqThry ^. Eq.waist)
      pconstrs = map (\(c,i) -> constrToPConstr c wst i) $ zip  constrs [0..length constrs]
  in PEqTheory (eqThry ^. Eq.thyName) 
     (head pconstrs)
     (take (length ftyps) (drop 1 pconstrs))
     (take (length axms) (drop (1 + length ftyps) pconstrs)) 

-- If the constr is a param, qualify it with an index, (like A1 and A2) 
-- If not, qualify with the instance name  (like (op M1)) 
mkPExpr :: PConstr -> (Name_,Int) -> Expr 
mkPExpr (PConstr nm _ True) (_,indx) = createId (nm ++ show indx)
mkPExpr (PConstr nm _ False) (instNm,_) = App [mkArg nm, mkArg instNm] 

