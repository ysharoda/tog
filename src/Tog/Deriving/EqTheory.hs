{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.EqTheory
  ( EqTheory
  , thyName
  , waist
  , sort
  , funcTypes
  , axioms
  , args
  , params
  , toDecl
  , build
  ) where 

import Data.Generics as Generics(Data)
import Control.Lens

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
  _thyName   :: Name_  ,
  _sort       :: Constr , 
  _funcTypes  :: [Constr],
  _axioms     :: [Constr],
  _waist      :: Waist }
  deriving (Data)

makeLenses ''EqTheory

decls :: EqTheory -> [Constr]
decls t = t^.sort : t^.funcTypes ++ t^.axioms

args :: EqTheory -> [Constr]
args t = take (t^.waist) $ decls t

params :: EqTheory -> Params
params = mkParams . map fldsToBinding . args

toDecl :: (Name_ -> Name_) -> EqTheory -> Decl
toDecl ren t =
  let nm = t^.thyName in
  Record (mkName nm) (params t)
    (RecordDeclDef setType (mkName $ ren nm)
      (mkField $ drop (t^.waist) (decls t)))

build :: Name_ -> Constr -> [Constr] -> [Constr] -> Waist -> EqTheory
build = EqTheory
