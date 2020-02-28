module Tog.AbstractTypes where

import Tog.Raw.Abs 
import Tog.TUtils 

-- uni sorted equational theory
-- the waist determines how many parameters we have in the theory, like in Musa's work
type Waist = Int

-- Becuase the declarations are telescopes, a theory with waist n, has the first n declarations as parameters. 
data EqTheory = EqTheory {
  getThryName       :: Name_  ,
  getSort       :: Constr , 
  getFuncTypes  :: [Constr],
  getAxioms     :: [Constr],
  getWaist      :: Waist } 

getSortName :: EqTheory -> Name_ 
getSortName eqThry = getConstrName $ getSort eqThry

thryArgs :: EqTheory -> [Constr]
thryArgs thry =
  let decls = [getSort thry] ++ (getFuncTypes thry) ++ (getAxioms thry) 
  in  take (getWaist thry) decls

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

createThryInsts :: EqTheory -> [Binding]
createThryInsts eqThry =
 let thryInstName index = createId $ genCharName (getThryName eqThry) index
 in [Bind [Arg (thryInstName 1)]
          (createThryInstType (getThryName eqThry) (thryArgs eqThry) 1) ,
     Bind [Arg (thryInstName 2)]
          (createThryInstType (getThryName eqThry) (thryArgs eqThry) 2) ]

{- ---------------- The  Hom Function ------------------ -}

genHomFunc :: Bool -> Name_ -> Name_ -> Name_  -> Constr 
genHomFunc isQualified sortName inst1Name inst2Name =
  Constr (Name (noSrcLoc,"hom"))
   $ if isQualified
     then Fun (qualDecl sortName inst1Name)   (qualDecl sortName inst2Name)
     else Fun (notQualDecl $ sortName ++ "1") (notQualDecl $ sortName ++ "2") 
             
{- ------------ Preservation Axioms ----------------- -}

-- presAxioms :: FuncType -> Axiom 

genPresAxioms :: EqTheory -> [Constr]
genPresAxioms _ = [] 

{- ------------ The Hom Record -------------------- -}

homomorphism :: EqTheory -> HomThry 
homomorphism eqThry =
  let -- instances and instNames should both have length exactly 2
    instances = (createThryInsts eqThry)
    (instName1 , instName2)  =
      let names = concatMap getBindingArgNames instances
      in if length names == 2 then (head names, last names)
         else error "Generating Hom: Error while creating recod isntances" 
  in HomThry
      (getThryName eqThry ++ "Hom")
      (map (genInstParams True) (thryArgs eqThry))
      instances 
      (genHomFunc (length (thryArgs eqThry) /= 0) (getConstrName $ getSort eqThry) instName1 instName2)
      (genPresAxioms eqThry) 
         
