module Tog.Deriving.Utils.Bindings
  (mkBinding,
   indexOneBind,
   indexBindings, 
   repeatBinds,
   getOneBindNames,
   getBindingsNames) where 

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

-- function bindings 
mkBinding :: PConstr -> PConstr -> (Name_,Int) -> Char -> [Binding]
mkBinding carrier fdecl (instName, index) sym  =
  let vars = mkBindVars fdecl sym
      typs = mkBindExpr carrier fdecl (instName, index)
  in zipWith (\v ty -> HBind [v] ty) vars typs

-- we need the isHidden flag, because we cannot infer if a function argument is hidden or not based on whether it is hidden or not in the datatype (eg: in the case of closed term langauge)  
indexOneBind :: Bool -> Int -> Binding -> Binding 
indexOneBind isHidden i (Bind  as e) =
 let newArgs =  map (indexArg i) as
 in if (isHidden) then HBind newArgs e else Bind newArgs e 
indexOneBind isHidden i (HBind as e) =
 let newArgs =  map (indexArg i) as
 in if (isHidden) then HBind newArgs e else Bind newArgs e

indexBindings :: Bool -> Int -> [Binding] -> [Binding]
indexBindings isHidden i binds = map (indexOneBind isHidden i) binds 

repeatBinds :: Int -> [Binding] -> [Binding]
repeatBinds 0 _ = [] 
repeatBinds 1 binds = binds
repeatBinds num binds =
  [indexOneBind True i b | b <- binds, i <- [1 .. num]]

getOneBindNames :: Binding -> [Name_]
getOneBindNames (Bind  as _) = map (\a -> getArgName a) as
getOneBindNames (HBind as _) = map (\a -> getArgName a) as

getBindingsNames :: [Binding] -> [Name_]
getBindingsNames binds = concatMap getOneBindNames binds
