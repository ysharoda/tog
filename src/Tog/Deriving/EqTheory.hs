module Tog.Deriving.EqTheory
  ( EqTheory(EqTheory, thryName, sort, funcTypes, waist, axioms)
  , args
  , params
  , toDecl
  ) where 

import Data.Generics as Generics(Data)

import Tog.Raw.Abs   
import Tog.Deriving.Types  (Name_)
import Tog.Deriving.TUtils (mkParams, fldsToBinding, mkName, mkField, setType)

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
decls t = sort t : funcTypes t ++ axioms t

args :: EqTheory -> [Constr]
args thry = take (waist thry) $ decls thry

params :: EqTheory -> Params
params = mkParams . map fldsToBinding . args

toDecl :: (Name_ -> Name_) -> EqTheory -> Decl
toDecl ren t =
  let nm = thryName t in
  Record (mkName nm) (params t)
    (RecordDeclDef setType (mkName $ ren nm)
      (mkField $ drop (waist t) (decls t)))
