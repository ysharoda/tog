module Tog.Deriving.Utils.Bindings (mkBinding) where 

import Tog.Raw.Abs

import qualified Tog.Deriving.PEqTheory as PEq 
import           Tog.Deriving.Types (Name_)
import           Tog.Deriving.TUtils 

mkBindExpr :: PEq.PConstr -> PEq.PConstr -> (Name_,Int) -> [Expr]
mkBindExpr carrier (PEq.PConstr _ typ _) (instName,index) =
  let argNm = PEq.mkPExpr carrier (instName,index)
  in take (exprArity typ) $ repeat argNm 
    
mkBindVars :: PEq.PConstr -> Char -> [Arg]
mkBindVars (PEq.PConstr _ typ _) sym = map mkArg $ genVarsWSymb sym $ exprArity typ

mkBinding :: PEq.PConstr -> PEq.PConstr -> (Name_,Int) -> Char -> [Binding]
mkBinding carrier fdecl (instName, index) sym  =
  let vars = mkBindVars fdecl sym
      typs = mkBindExpr carrier fdecl (instName, index)
  in zipWith (\v ty -> HBind [v] ty) vars typs
