module Tog.Deriving.Hom
 ( homomorphism
 ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs 
import           Tog.Deriving.TUtils 
import           Tog.Deriving.Types (Name_)
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name)

type FuncType = Constr
type Axiom = Constr 

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
      (n1, n2) = (shortName nam 1, shortName nam 2) in
  ((Bind [mkArg n1] (declTheory nam (Eq.args t) 1), n1) ,
   (Bind [mkArg n2] (declTheory nam (Eq.args t) 2), n2) )

{- ---------------- The  Hom Function ------------------ -}

genHomFunc :: Bool -> Name_ -> Name_ -> Name_  -> Constr 
genHomFunc isQualified sortName inst1Name inst2Name =
  Constr (mkName homFuncName)
   $ if isQualified
     then Fun (qualDecl sortName inst1Name)   (qualDecl sortName inst2Name)
     else Fun (notQualDecl $ sortName ++ "1") (notQualDecl $ sortName ++ "2") 
             
{- ------------ Preservation Axioms ----------------- -}

genPresAxioms :: Eq.EqTheory -> [Constr]
genPresAxioms eqthry = 
  let nparms = eqthry ^. Eq.waist - 1
      decls  = eqthry ^. Eq.funcTypes
      (args, flds) = splitAt nparms decls
      n = eqthry ^. Eq.thyName
  in (map (oneAxiom n True) args) ++ 
     (map (oneAxiom n False) flds)
  
-- e : A 
oneAxiom :: Name_ -> Bool -> FuncType -> Axiom 
oneAxiom n isParam c@(Constr nm typ) =
  Constr (mkName $ "pres-" ++ nm^.name)
   (Pi (Tel $ genBinding n isParam typ) (genEq n c))       

genBinding :: Name_ -> Bool -> Expr -> [Binding]
genBinding n isParam expr =
 let vars =  map mkArg $ genVars $ exprArity expr
     instName = shortName n 1
     argQualName arg =
       if isParam 
       then notQualDecl (getArgName arg ++ "1")
       else qualDecl (getArgName arg) instName
     -- A list of types in the expression 
     exprTypes (App arg) = map argQualName arg
     exprTypes (Fun e1 e2) = (exprTypes e1) ++ (exprTypes e2)
     exprTypes _ = error "invalid expression"
 in zipWith (\v ty -> HBind [v] ty) vars (exprTypes expr)

genLHS :: (Constr -> Expr) -> Constr -> Expr
genLHS build constr@(Constr _ expr) =
 let (App homFuc)   = notQualDecl homFuncName 
     (App funcName) = build constr
     vars  = map mkArg $ genVars $ exprArity expr
     funcApp = case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> (Arg $ App funcName):vars
       Fun _ _  -> [Arg $ App $ (Arg $ App funcName):vars]
       x -> error $ "Invalid expr " ++ show x
 in App $ homFuc ++ funcApp 

genRHS ::  (Constr -> Expr) -> Constr -> Expr
genRHS build constr@(Constr _ expr) =
  let vars = map mkArg $ genVars $ exprArity expr
      args = map (\x -> Arg $ App [mkArg homFuncName, x]) vars
  in App $ [Arg $ build constr] ++ args 

mkDecl :: Name_ -> Constr -> Expr
mkDecl n c = qualDecl (getConstrName c) n

genEq :: Name_ -> Constr -> Expr
genEq n constr =
  Eq (genLHS (mkDecl $ shortName n 1) constr)
     (genRHS (mkDecl $ shortName n 2) constr) 

{- ------------ The Hom Record -------------------- -}

homomorphism :: Eq.EqTheory -> Decl
homomorphism t =
  let ((i1, n1), (i2, n2)) = createThryInsts t
      a = Eq.args t 
      nm = t ^. Eq.thyName ++ "Hom"
      fnc = genHomFunc (length a == 0) (getConstrName $ t^.Eq.sort) n1 n2
      axioms = genPresAxioms t
  in Record (mkName nm)
   (mkParams $ [i1, i2] ++ map (recordParams Bind) a)
   (RecordDeclDef setType (mkName $ nm ++ "C") (mkField $ fnc : axioms))
