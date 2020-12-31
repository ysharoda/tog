-- reference the paper: "Dynamic IFC Theorems for Free!" by Algehed, Bernardy, and Hritcu
-- arXiv: https://arxiv.org/pdf/2005.04722.pdf

module Interpret.Deriving.RelationalInterp where 

import           Control.Lens ((^.))

import           Tog.Raw.Abs 
import           Interpret.Utils.TUtils 
import qualified Interpret.Deriving.EqTheory  as Eq
import           Interpret.Utils.Lenses   (name)
import           Interpret.Utils.Functions (curryExpr)
import           Interpret.Utils.Bindings 

interpTypeName :: Name_
interpTypeName = "interp"

{- --------- The interpretation definitions ------------------- -} 

-- create the interpretation type
mkInterpType :: Eq.EqTheory -> Eq.EqInstance -> Eq.EqInstance -> Constr -> Constr
mkInterpType thry i1 i2 carrier =
  Constr (mkName interpTypeName) $ 
   Fun (Eq.projectConstr thry i1 carrier) $ 
     Fun (Eq.projectConstr thry i2 carrier) setTypeAsId

{- ------------- generate the interpretation declaration ---------- -}
-- the new one
interpretation :: Eq.EqTheory -> Eq.EqInstance -> Eq.EqInstance -> Constr -> Constr -> Constr 
interpretation thry i1 i2 (Constr interpName _) constr@(Constr fsym _) =
  let (bind1,expr1) = Eq.applyProjConstr thry i1 constr (Just 'x')
      (bind2,expr2) = Eq.applyProjConstr thry i2 constr (Just 'y')
      args1 = concatMap getBindingArgs bind1 ++ [Arg expr1]
      args2 = concatMap getBindingArgs bind2 ++ [Arg expr2]
      fexpr = zipWith (\x y -> App [mkArg (interpName ^. name),x,y]) args1 args2  
  in Constr (mkName $ "interp-" ++ fsym ^. name) $
        if (null $ bind1 ++ bind2) then curryExpr fexpr 
        else Pi (Tel $ bind1 ++ bind2) $ curryExpr fexpr

{- -------- The RelationalInterp record -------------- -}

relationalInterp :: Eq.EqTheory -> Decl
relationalInterp thry =
  let nm = "RelInterp"
      i1@(n1,b1,e1) = Eq.eqInstance thry (Just 1) 
      i2@(n2,b2,e2) = Eq.eqInstance thry (Just 2)
      interpType = mkInterpType thry i1 i2 (thry ^. Eq.sort)
      newDecls = map (interpretation thry i1 i2 interpType) (thry ^. Eq.funcTypes) 
  in Record (mkName nm)
      (mkParams $ b1 ++ b2 ++ map (\(n,e) -> Bind [mkArg n] e) [(n1,e1),(n2,e2)])
      (RecordDeclDef setType (mkName $ nm ++ "C")
          (Fields $ interpType : newDecls))
