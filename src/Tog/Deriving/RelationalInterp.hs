-- reference the paper: "Dynamic IFC Theorems for Free!" by Algehed, Bernardy, and Hritcu
-- arXiv: https://arxiv.org/pdf/2005.04722.pdf

module Tog.Deriving.RelationalInterp where 

import           Control.Lens ((^.))

import           Tog.Raw.Abs 
import           Tog.Deriving.TUtils 
import           Tog.Deriving.Types (Name_)
import qualified Tog.Deriving.EqTheory  as Eq
import           Tog.Deriving.Lenses   (name)
import           Tog.Deriving.Utils.Bindings 
import           Tog.Deriving.Utils.Parameters
import           Tog.Deriving.Utils.QualDecls

interpTypeName :: Name_
interpTypeName = "interp"

{- --------- The interpretation definitions ------------------- -} 

-- create the interpretation type 
mkTwoParamsType :: PConstr -> Name_ -> Name_ -> Constr
mkTwoParamsType srt param1 param2 =
  Constr (mkName interpTypeName) $
    Fun (mkPExpr srt (param1,1)) $ Fun (mkPExpr srt (param2,2)) setTypeAsId 

-- Generate the type instance for individual args, based on the arity of the operation
-- for example, for a binary operation with bindings [x1,x2] and [y1,y2],
-- this function generates: [Interp x1 y1, Interp x2 y2]
mkParam1 :: Constr -> [Arg] -> [Arg] -> [Expr] 
mkParam1 (Constr nm _) vars1 vars2 =
  let iTyp = mkArg $ nm^.name
      pairs = zip vars1 vars2
   in map (\(x,y) -> App [iTyp,x,y]) pairs

-- first argument: Interpretation function
-- Generate the type instance for the interpretation function applied to the result of the operation symbol
-- for example, for a binary operation with binding [x1,x2] and [y1,y2],
-- the function generates: Interp (op x1 x2) (op y1 y2) 
mkParam2 :: Constr -> [Arg] -> [Arg] -> Name_ -> Name_ -> PConstr -> Expr
mkParam2 (Constr inm _) vars1 vars2 inst1 inst2 func =
  let iTyp = mkArg $ inm ^. name
      fnm1 = mkPExpr func (inst1,1)
      fnm2 = mkPExpr func (inst2,2)
      farg1 = App $ [Arg fnm1] ++ vars1
      farg2 = App $ [Arg fnm2] ++ vars2
   in App [iTyp,Arg farg1,Arg farg2]     

{- ------------- generate the interpretation declaration ---------- -}
-- the new one 
oneInterp :: Constr -> PConstr -> Name_ -> Name_ ->  PConstr -> Constr
oneInterp interpFunc carrier inst1 inst2 fsym@(PConstr nm _ _) =
  let [binds1,binds2] = map (\(x,y) -> mkBinding carrier fsym x y) [((inst1,1),'x'),((inst2,2),'y')]  
      [args1,args2] = map (concatMap getBindingArgs) [binds1,binds2] 
  in Constr (mkName $ "interp-" ++ nm) $ 
   Pi (Tel $ binds1 ++ binds2) $ 
     mkFunc $ (mkParam1 interpFunc args1 args2) ++  [mkParam2 interpFunc args1 args2 (inst1) (inst2) fsym]

{- -------- The RelationalInterp record -------------- -}

relationalInterp :: Eq.EqTheory -> Decl
relationalInterp t =
  let nm = t ^. Eq.thyName ++ "RelInterp"
      (psort,pfuncs,_) = Eq.mkPConstrs t
      ((i1, n1), (i2, n2)) = createThryInsts t
      interpTyp = mkTwoParamsType psort n1 n2 
      newDecls = map (oneInterp interpTyp psort n1 n2) pfuncs
  in Record (mkName nm)
      (mkParams $ (map (recordParams Bind) (Eq.args t)) ++ [i1,i2])
      (RecordDeclDef setType (mkName $ nm ++ "C")
          (Fields $ interpTyp : newDecls))
