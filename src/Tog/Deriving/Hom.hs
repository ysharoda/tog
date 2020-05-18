module Tog.Deriving.Hom
 ( homomorphism
 , createThryInsts
 , recordParams 
 ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs 
import           Tog.Deriving.TUtils
import           Tog.Deriving.Utils (getBindingArgs) 
import           Tog.Deriving.Types (Name_)
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name)
import           Tog.Deriving.Utils.Bindings 
import qualified Tog.Deriving.PEqTheory as PEq

homFuncName :: String 
homFuncName = "hom"

mkArg' :: Name_ -> Int -> Arg
mkArg' nam n = mkArg $ shortName nam n

{- --------- The Parameters of the hom record ----------------- -} 

recordParams :: ([Arg] -> Expr -> Binding) -> Constr -> Binding
recordParams bind (Constr nm typ) =
  let n = nm^.name in bind [mkArg' n 1, mkArg' n 2] typ

createThryInsts :: Eq.EqTheory -> ((Binding, Name_), (Binding, Name_))
createThryInsts t =
  let nam = t ^. Eq.thyName
      (n1, n2) = (twoCharName nam 1, twoCharName nam 2) in
  ((Bind [mkArg n1] (declTheory nam (Eq.args t) 1), n1) ,
   (Bind [mkArg n2] (declTheory nam (Eq.args t) 2), n2) )

{- ---------------- The  Hom Function ------------------ -}

genHomFunc :: PEq.PConstr -> Name_ -> Name_ -> Constr 
genHomFunc srt inst1Name inst2Name =
  Constr (mkName homFuncName) $ 
   Fun (PEq.mkPExpr srt (inst1Name,1)) (PEq.mkPExpr srt (inst2Name,2))            

{- ------------ Preservation Axioms -------------------- -}

oneAxiom :: Constr -> PEq.PConstr -> Name_ -> Name_ ->  PEq.PConstr -> Constr
oneAxiom homFunc carrier inst1 inst2 fsym@(PEq.PConstr nm _ _) =
  let binds = mkBinding carrier fsym (inst1,1) 'x'
      args = concatMap getBindingArgs binds 
  in Constr (mkName $ "pres-" ++ nm) $
      Pi (Tel $ binds) (genEq homFunc args inst1 inst2 fsym)
      
genLHS :: Constr -> [Arg] -> Name_ -> PEq.PConstr -> Expr
genLHS (Constr fnm _) vars inst1 func =
  let hom = mkArg $ fnm ^. name
      fnm1 = PEq.mkPExpr func (inst1,1)
      farg1 = App $ [Arg fnm1] ++ vars
  in App [hom,Arg farg1] 

genRHS :: Constr -> [Arg] -> Name_ -> PEq.PConstr -> Expr
genRHS (Constr fnm _) vars inst2 fsym =
  let hom = mkArg $ fnm ^. name
      func = PEq.mkPExpr fsym (inst2,2)
      fargs = map (\x -> App [hom,x]) vars
  in App $ (Arg func) : (map Arg fargs)

genEq :: Constr -> [Arg] -> Name_ -> Name_ -> PEq.PConstr -> Expr
genEq homFunc args inst1 inst2 pconstr =
  Eq (genLHS homFunc args inst1 pconstr)
     (genRHS homFunc args inst2 pconstr) -- (mkDecl inst2) pconstr) 

{- ------------ The Hom Record -------------------- -}

homomorphism :: Eq.EqTheory -> Decl
homomorphism t =
  let nm = t ^. Eq.thyName ++ "Hom"
      peqThry = PEq.eqToPEqTheory t
      psort = peqThry ^. PEq.sort 
      pfuncs = peqThry ^. PEq.funcTypes
      ((i1, n1), (i2, n2)) = createThryInsts t
      a = Eq.args t 
      fnc = genHomFunc psort n1 n2
      axioms = map (oneAxiom fnc psort n1 n2) pfuncs 
  in Record (mkName nm)
   (mkParams $ (map (recordParams Bind) a) ++ [i1,i2])
   (RecordDeclDef setType (mkName $ nm ++ "C") (mkField $ fnc : axioms))
