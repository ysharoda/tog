module Tog.Deriving.Utils.Bindings (mkBinding) where 

import Tog.Raw.Abs

import Tog.Deriving.Utils.QualDecls 
import Tog.Deriving.Types (Name_)
import Tog.Deriving.TUtils 

mkBindExpr :: PConstr -> PConstr -> (Name_,Int) -> [Expr]
mkBindExpr carrier (PConstr _ typ _) (instName,index) =
  let argNm = mkPExpr carrier (instName,index)
  in take (exprArity typ) $ repeat argNm 
    
mkBindVars :: PConstr -> Char -> [Arg]
mkBindVars (PConstr _ typ _) sym = map mkArg $ genVarsWSymb sym $ exprArity typ

mkBinding :: PConstr -> PConstr -> (Name_,Int) -> Char -> [Binding]
mkBinding carrier fdecl (instName, index) sym  =
  let vars = mkBindVars fdecl sym
      typs = mkBindExpr carrier fdecl (instName, index)
  in zipWith (\v ty -> HBind [v] ty) vars typs
