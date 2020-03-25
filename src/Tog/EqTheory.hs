module Tog.EqTheory where 

import Tog.Raw.Abs   
import Tog.TUtils (Name_, getConstrName)
import Data.Generics as Generics(Data)

-- uni sorted equational theory
-- the waist determines how many parameters we have in the theory, 
-- like in Musa's work
type Waist = Int

-- Because the declarations are telescopes, a theory with waist n, 
-- has the first n declarations as parameters. 
data EqTheory = EqTheory {
  thryName   :: Name_  ,
  sort       :: Constr , 
  funcTypes  :: [Constr],
  axioms     :: [Constr],
  waist      :: Waist }
  deriving (Data)

getSortName :: EqTheory -> Name_ 
getSortName = getConstrName . sort

decls :: EqTheory -> [Constr]
decls thry = sort thry : (funcTypes thry) ++ (axioms thry) 

thryArgs :: EqTheory -> [Constr]
thryArgs thry = take (waist thry) $ decls thry

thryFields :: EqTheory -> [Constr]
thryFields thry = drop (waist thry) $ decls thry
