module Tog.EqTheory where 

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
  getWaist      :: Waist } deriving (Show,Eq) 

getSortName :: EqTheory -> Name_ 
getSortName eqThry = getConstrName $ getSort eqThry

thryArgs :: EqTheory -> [Constr]
thryArgs thry =
  let decls = [getSort thry] ++ (getFuncTypes thry) ++ (getAxioms thry) 
  in  take (getWaist thry) decls

thryFields :: EqTheory -> [Constr]
thryFields thry =
  let decls = [getSort thry] ++ (getFuncTypes thry) ++ (getAxioms thry) 
  in  drop (getWaist thry) decls
