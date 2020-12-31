module Interpret.Deriving.Hom (homomorphism) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs 
import           Interpret.Utils.TUtils
import qualified Interpret.Deriving.EqTheory as Eq
import           Interpret.Utils.Lenses   (name)
import           Interpret.Utils.Functions 

homFuncName :: String 
homFuncName = "hom"

{- ---------------- The  Hom Function ------------------ -}

homFunc :: Eq.EqTheory -> Eq.EqInstance -> Eq.EqInstance -> Constr -> Constr 
homFunc thry i1 i2 carrier =
  Constr (mkName homFuncName) $
    Fun (Eq.projectConstr thry i1 carrier) (Eq.projectConstr thry i2 carrier)  

{- ------------ Preservation Axioms -------------------- -}

presAxiom :: Eq.EqTheory -> Eq.EqInstance -> Eq.EqInstance -> Constr -> Constr -> Constr 
presAxiom thry i1 i2 hom c@(Constr n _) =
  Constr (mkName $ "pres-" ++ n ^. name) $
     equation thry i1 i2 hom c 
       
-- the second argument is the expression resulting from fapp 
-- the first argument is the hom function.
lhs :: Constr -> Expr -> Expr
lhs (Constr n _) fexpr =
  App [mkArg (n ^. name),Arg fexpr]

rhs :: Constr -> Expr -> Expr
rhs (Constr n _) fexpr =
  functor (n ^. name) fexpr 

equation :: Eq.EqTheory -> Eq.EqInstance -> Eq.EqInstance -> Constr -> Constr -> Expr 
equation thry i1 i2 hom constr =
  let (bind1,expr1) = Eq.applyProjConstr thry i1 constr Nothing
      (_,expr2) = Eq.applyProjConstr thry i2 constr Nothing 
  in if bind1 == [] then Eq (lhs hom expr1) (rhs hom expr2)
     else Pi (Tel bind1) $ Eq (lhs hom expr1) (rhs hom expr2)

{- ------------ The Hom Record -------------------- -}

homomorphism :: Eq.EqTheory -> Decl
homomorphism thry =
  let nm = "Hom" 
      i1@(n1,b1,e1) = Eq.eqInstance thry (Just 1) 
      i2@(n2,b2,e2) = Eq.eqInstance thry (Just 2)
      fnc = homFunc thry i1 i2 (thry ^. Eq.sort)
      axioms = map (presAxiom thry i1 i2 fnc) (thry ^. Eq.funcTypes)  
  in Record (mkName nm)
   (mkParams $ b1 ++ b2 ++ map (\(n,e) -> Bind [mkArg n] e) [(n1,e1),(n2,e2)])
   (RecordDeclDef setType (mkName $ nm ++ "C") (mkField $ fnc : axioms))

   
