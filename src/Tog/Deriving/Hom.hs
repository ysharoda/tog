module Tog.Deriving.Hom where

import           Tog.Raw.Abs 
import           Tog.Deriving.TUtils 
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
      
{- --------- The Parameters of the hom record ----------------- -} 
  
genInstParams :: Bool -> Constr -> Binding
genInstParams isHidden (Constr name typ) =
  let arg1 = Arg $ createId $ genCharName (getNameAsStr name) 1
      arg2 = Arg $ createId $ genCharName (getNameAsStr name) 2
  in if isHidden then (HBind [arg1,arg2] typ) else (Bind [arg1,arg2] typ)

thryInstName :: Name_ -> Int -> Name_ 
thryInstName thryName index = genCharName thryName index

createThryInsts :: Eq.EqTheory -> [Binding]
createThryInsts eqThry =
  [Bind [Arg $  createId $ thryInstName (Eq.thryName eqThry) 1]
        (createThryInstType (Eq.thryName eqThry) (Eq.thryArgs eqThry) 1) ,
   Bind [Arg $  createId $ thryInstName (Eq.thryName eqThry) 2]
        (createThryInstType (Eq.thryName eqThry) (Eq.thryArgs eqThry) 2) ]

{- ---------------- The  Hom Function ------------------ -}

genHomFunc :: Bool -> Name_ -> Name_ -> Name_  -> Constr 
genHomFunc isQualified sortName inst1Name inst2Name =
  Constr (mkName homFuncName)
   $ if isQualified
     then Fun (qualDecl sortName inst1Name)   (qualDecl sortName inst2Name)
     else Fun (notQualDecl $ sortName ++ "1") (notQualDecl $ sortName ++ "2") 
             
{- ------------ Preservation Axioms ----------------- -}

-- presAxioms :: FuncType -> Axiom 

-- Change the names of the parameters t
applyConstr :: Name_ -> Bool -> Constr -> Expr
applyConstr thryName isParam constr =
  if isParam then qualDecl (getConstrName constr) (thryName)
  else notQualDecl (getConstrName constr)  

genPresAxioms :: Eq.EqTheory -> [Constr]
genPresAxioms eqthry = 
  let decls = Eq.funcTypes eqthry
      args = take ((Eq.waist eqthry) - 1) decls
      flds = drop ((Eq.waist eqthry) - 1) decls  
  in (map (oneAxiom (Eq.thryName eqthry) True) $ args)
  ++  (map (oneAxiom (Eq.thryName eqthry) False) $ flds)
  
-- e : A 
oneAxiom :: Name_ -> Bool -> FuncType -> Axiom 
oneAxiom thryName isParam c@(Constr name typ) =
  Constr (mkName $ "pres-" ++ getNameAsStr name)
   (Pi (Tel $ genBinding thryName isParam typ) (genEq thryName isParam c))       

{-
argQualName instName isParam arg =
        if isParam then map (\n -> qualDecl n instName) (getArgName arg)
        else map notQualDecl (getArgName arg)
-}
genBinding :: Name_ -> Bool -> Expr -> [Binding]
genBinding thryName isParam expr =
 let vars =  map (\x -> Arg $ createId x) $ genVars $ exprArity expr
     instName = thryInstName thryName 1
     argQualName arg =
        if isParam then map (\x -> notQualDecl (x ++ "1")) (getArgName arg)
        else map (\n -> qualDecl n instName) (getArgName arg)
     -- A list of types in the expression 
     exprTypes (App arg) = concatMap argQualName arg
     exprTypes (Fun e1 e2) = (exprTypes e1) ++ (exprTypes e2)
     exprTypes _ = error "invalid expression"
 in zipWith (\v ty -> HBind [v] ty) vars (exprTypes expr)

genHomFuncApp :: Name_ -> Bool -> Constr -> Expr
genHomFuncApp instName isParam constr@(Constr _ expr) =
 let (App homFuc)   = notQualDecl homFuncName 
     (App funcName) =
       if isParam then notQualDecl (getConstrName constr)
       else qualDecl (getConstrName constr) instName
     vars  = map (\x -> createId x) $ genVars $ exprArity expr
     funcApp = case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> map Arg $ (App funcName):vars
       Fun _ _  -> [Arg $ App $ map Arg $ (App funcName):vars]
       x -> error $ "Invalid expr " ++ show x
 in App $ homFuc ++ funcApp 

{-
(App [Arg (Id (NotQual (Name ((17,14),"h")))),Arg (App [Arg (Id (NotQual (Name ((17,17),"e")))),Arg (Id (NotQual (Name ((17,19),"M1"))))])]) 

-} 

genHomFuncArg :: Constr -> Name_ -> [Arg]
genHomFuncArg (Constr name expr) instName =
  -- qualifying by the instance name  
  let funcName = App [Arg $ createId (getNameAsStr name), Arg $ createId instName] 
      vars  = map (\x -> createId x) $ genVars $ exprArity expr
   in case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> map Arg $ funcName:vars
       Fun _ _  -> [Arg $ App $ map Arg $ funcName:vars]
       x -> error $ "Invalid expr " ++ show x

genLHS :: Name_ -> Bool -> Constr -> Expr
genLHS  instName isParam constr = genHomFuncApp instName isParam constr

genRHS ::  Name_ -> Bool -> Constr -> Expr
genRHS instName isParam constr@(Constr _ expr) =
  let funcName = if isParam then  notQualDecl (getConstrName constr) 
                 else qualDecl (getConstrName constr) instName
     -- vars  = map (\x -> createId x) $ genVars $ exprArity expr
      vars = map (\x -> createId x) $ genVars $ exprArity expr
      args = map (\x -> Arg $ App $ [Arg $ createId homFuncName, Arg x]) vars
   --   (App args) = 
    --    genHomFuncApp instName isParam constr
      -- args x =  error $ "Invalid expr " ++ show x
--      args (App [Arg a]) = args a
--      args (App (a:as)) = args (App [a]) ++ (args $ App as)
--      args (Fun e1 e2)  = args e1 ++ args e2  
  in App $ [Arg funcName] ++ args 

genEq :: Name_ -> Bool -> Constr -> Expr
genEq thryName isParam constr =
  let inst1Name = thryInstName thryName 1 
      inst2Name = thryInstName thryName 2
  in  Eq (genLHS inst1Name isParam constr)
         (genRHS inst2Name isParam constr) 

{- ------------ The Hom Record -------------------- -}

homomorphism :: Eq.EqTheory -> HomThry 
homomorphism eqThry =
  let -- instances and instNames should both have length exactly 2
    instances = (createThryInsts eqThry)
    (instName1 , instName2)  =
      let names = concatMap getBindingArgNames instances
      in if length names == 2 then (head names, last names)
         else error "Generating Hom: Error while creating recod isntances" 
  in HomThry
      (Eq.thryName eqThry ++ "Hom")
      (map (genInstParams True) (Eq.thryArgs eqThry))
      instances 
      (genHomFunc (length (Eq.thryArgs eqThry) == 0) (getConstrName $ Eq.sort eqThry) instName1 instName2)
      (genPresAxioms eqThry) 
         
