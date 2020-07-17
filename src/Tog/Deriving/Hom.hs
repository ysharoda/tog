module Tog.Deriving.Hom (homomorphism) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs 
import           Tog.Deriving.TUtils
import           Tog.Deriving.Types (Name_)
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name)
import           Tog.Deriving.Utils.Bindings
import           Tog.Deriving.Utils.Parameters
import           Tog.Deriving.Utils.QualDecls

homFuncName :: String 
homFuncName = "hom"

{- ---------------- The  Hom Function ------------------ -}

genHomFunc :: PConstr -> Name_ -> Name_ -> Constr 
genHomFunc srt inst1Name inst2Name =
  Constr (mkName homFuncName) $ 
   Fun (mkPExpr srt (inst1Name,1)) (mkPExpr srt (inst2Name,2))            

{- ------------ Preservation Axioms -------------------- -}

oneAxiom :: Constr -> PConstr -> Name_ -> Name_ ->  PConstr -> Constr
oneAxiom homFunc carrier inst1 inst2 fsym@(PConstr nm _ _) =
  let binds = mkBinding carrier fsym (inst1,1) 'x'
      args = concatMap getBindingArgs binds 
  in Constr (mkName $ "pres-" ++ nm) $
      Pi (Tel binds) (genEq homFunc args inst1 inst2 fsym)
      
genLHS :: Constr -> [Arg] -> Name_ -> PConstr -> Expr
genLHS (Constr fnm _) vars inst1 func =
  let hom = mkArg $ fnm ^. name
      fnm1 = mkPExpr func (inst1,1)
      farg1 = App $ Arg fnm1 : vars
  in App [hom,Arg farg1] 

genRHS :: Constr -> [Arg] -> Name_ -> PConstr -> Expr
genRHS (Constr fnm _) vars inst2 fsym =
  let hom = mkArg $ fnm ^. name
      func = mkPExpr fsym (inst2,2)
      fargs = map (\x -> App [hom,x]) vars
  in App $ Arg func : map Arg fargs

genEq :: Constr -> [Arg] -> Name_ -> Name_ -> PConstr -> Expr
genEq homFunc args inst1 inst2 pconstr =
  Eq (genLHS homFunc args inst1 pconstr)
     (genRHS homFunc args inst2 pconstr) -- (mkDecl inst2) pconstr) 

{- ------------ The Hom Record -------------------- -}

homomorphism :: Eq.EqTheory -> Decl
homomorphism t =
  let nm = t ^. Eq.thyName ++ "Hom"
      (psort,pfuncs,_) = Eq.mkPConstrs t
      ((i1, n1), (i2, n2)) = createThryInsts t
      a = Eq.args t 
      fnc = genHomFunc psort n1 n2
      axioms = map (oneAxiom fnc psort n1 n2) pfuncs 
  in Record (mkName nm)
   (mkParams $ map (recordParams Bind) a ++ [i1,i2])
   (RecordDeclDef setType (mkName $ nm ++ "C") (mkField $ fnc : axioms))
