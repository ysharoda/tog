module Tog.Deriving.EqTheory
  ( EqTheory(EqTheory, thryName, sort, funcTypes, waist, axioms)
  , args
  ) where 

import Data.Generics as Generics(Data)

import Tog.Raw.Abs   
import Tog.Deriving.Types  (Name_)

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

decls :: EqTheory -> [Constr]
decls thry = sort thry : funcTypes thry ++ axioms thry

args :: EqTheory -> [Constr]
args thry = take (waist thry) $ decls thry
