module Tog.Deriving.Hom where

import           Tog.Raw.Abs 
import           Tog.Deriving.TUtils 
import           Tog.Deriving.Types (Name_)
import qualified Tog.Deriving.EqTheory as Eq

type HiddenBinds = [Binding]
type ExplicitBinds = [Binding]
type FuncType = Constr
type Axiom = Constr 

data HomThry = HomThry {
  getHomName       :: Name_ ,
  getHiddenArgs    :: HiddenBinds,
  getExplictArgs   :: ExplicitBinds, 
  getHomFunc       :: Constr,
  getPresAxioms    :: [Constr] }
      
homFuncName :: String 
homFuncName = "hom"

mkArg' :: Name_ -> Int -> Arg
mkArg' nam n = mkArg $ shortName nam n

{- --------- The Parameters of the hom record ----------------- -} 

genInstParams :: ([Arg] -> Expr -> Binding) -> Constr -> Binding
genInstParams bind (Constr name typ) =
  let n = name_ name in bind [mkArg' n 1, mkArg' n 2] typ

createThryInsts :: Eq.EqTheory -> [Binding]
createThryInsts t =
  let nam = Eq.thryName t in
  [Bind [mkArg' nam 1] (createThryInstType nam (Eq.args t) 1) ,
   Bind [mkArg' nam 2] (createThryInstType nam (Eq.args t) 2) ]

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
  let parms = Eq.waist eqthry - 1
      decls = Eq.funcTypes eqthry
      (args, flds) = splitAt parms decls
  in (map (oneAxiom (Eq.thryName eqthry) True) args) ++ 
     (map (oneAxiom (Eq.thryName eqthry) False) flds)
  
-- e : A 
oneAxiom :: Name_ -> Bool -> FuncType -> Axiom 
oneAxiom thryName isParam c@(Constr name typ) =
  Constr (mkName $ "pres-" ++ name_ name)
   (Pi (Tel $ genBinding thryName isParam typ) (genEq thryName c))       

genBinding :: Name_ -> Bool -> Expr -> [Binding]
genBinding thryName isParam expr =
 let vars =  map mkArg $ genVars $ exprArity expr
     instName = shortName thryName 1
     argQualName arg =
       if isParam 
       then map (\x -> notQualDecl (x ++ "1")) (getArgName arg)
       else map (\n -> qualDecl n instName) (getArgName arg)
     -- A list of types in the expression 
     exprTypes (App arg) = concatMap argQualName arg
     exprTypes (Fun e1 e2) = (exprTypes e1) ++ (exprTypes e2)
     exprTypes _ = error "invalid expression"
 in zipWith (\v ty -> HBind [v] ty) vars (exprTypes expr)

genHomFuncApp :: (Constr -> Expr) -> Constr -> Expr
genHomFuncApp build constr@(Constr _ expr) =
 let (App homFuc)   = notQualDecl homFuncName 
     (App funcName) = build constr
     vars  = map mkArg $ genVars $ exprArity expr
     funcApp = case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> (Arg $ App funcName):vars
       Fun _ _  -> [Arg $ App $ (Arg $ App funcName):vars]
       x -> error $ "Invalid expr " ++ show x
 in App $ homFuc ++ funcApp 

genHomFuncArg :: Constr -> Name_ -> [Arg]
genHomFuncArg (Constr name expr) instName =
  -- qualifying by the instance name  
  let funcName = qualDecl (name_ name) instName
      vars  = map mkArg $ genVars $ exprArity expr
   in case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> Arg funcName:vars
       Fun _ _  -> [Arg $ App $ (Arg funcName:vars)]
       x -> error $ "Invalid expr " ++ show x

genLHS ::  (Constr -> Expr) -> Constr -> Expr
genLHS = genHomFuncApp

genRHS ::  (Constr -> Expr) -> Constr -> Expr
genRHS build constr@(Constr _ expr) =
  let vars = map mkArg $ genVars $ exprArity expr
      args = map (\x -> Arg $ App [mkArg homFuncName, x]) vars
  in App $ [Arg $ build constr] ++ args 

mkDecl :: Name_ -> Constr -> Expr
-- mkDecl True  _ c = notQualDecl $ getConstrName c
mkDecl n c = qualDecl (getConstrName c) n

genEq :: Name_ -> Constr -> Expr
genEq n constr =
  let n1 = shortName n 1 
      n2 = shortName n 2
  in  Eq (genLHS (mkDecl n1) constr)
         (genRHS (mkDecl n2) constr) 

{- ------------ The Hom Record -------------------- -}

homomorphism :: Eq.EqTheory -> HomThry 
homomorphism eqThry =
  let -- instances and instNames should both have length exactly 2
    instances = createThryInsts eqThry
    (instName1 , instName2)  =
      let names = concatMap getBindingArgNames instances
      in if length names == 2 then (head names, last names)
         else error "Generating Hom: Error while creating recod isntances" 
  in HomThry
      (Eq.thryName eqThry ++ "Hom")
      (map (genInstParams Bind) (Eq.args eqThry))
      instances 
      (genHomFunc (length (Eq.args eqThry) == 0) (getConstrName $ Eq.sort eqThry) instName1 instName2) 
      (genPresAxioms eqThry) 
