{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.EqTheory
  ( PConstr
  , pconstr 
  , pname
  , ptype
  , isParam
  , toConstr
  , EqTheory
  , thyName
  , sort
  , funcTypes
  , axioms
  , args
  , build 
  , instantiate 
  ) where 

import Data.Generics as Generics(Data)
import Control.Lens

import Tog.Raw.Abs   
import Tog.Deriving.Types  (Name_, gmap)
import Tog.Deriving.TUtils (mkParams, fldsToBinding, mkName, mkField, setType, twoCharName)
import Tog.Deriving.Lenses   (name)
import qualified Data.Map as Map
import Tog.Deriving.PConstr 

-- Because the declarations are telescopes, a theory with waist n, 
-- has the first n declarations as parameters. 
data EqTheory = EqTheory {
  _thyName    :: Name_  ,
  _sort       :: PConstr , 
  _funcTypes  :: [PConstr],
  _axioms     :: [PConstr]  }
  deriving (Data,Show)

makeLenses ''PConstr 
makeLenses ''EqTheory

toConstr :: PConstr -> Constr
toConstr (PConstr nm typ _) =
  Constr (mkName nm) typ 


decls :: EqTheory -> [PConstr]
decls t = t^.sort : t^.funcTypes ++ t^.axioms

args :: EqTheory -> [PConstr]
args t = takeWhile (\x -> x ^. isParam) $ decls t

waist :: EqTheory -> Int
waist t = length $ args t

params :: [Constr] -> Params
params constrs = mkParams $ map fldsToBinding constrs

build :: Name_ -> PConstr -> [PConstr] -> [PConstr] -> EqTheory
build nm srt fs axs =
  EqTheory nm srt fs axs 
{-
toDecl :: (Name_ -> Name_) -> EqTheory -> Decl
toDecl ren t =x
  let nm = t ^. thyName
      constrs = map toConstr $ decls t
  in
  Record (mkName nm) (params (take (waist t) constrs))
    (RecordDeclDef setType (mkName $ ren nm)
      (mkField $ drop (waist t) constrs))
-}
-- A constr when used is either:
-- 1. Indexed, in case it is a parameter to the theory
-- 2. Qualiifed, in case it is a field of the theory
-- In both cases, it is converted to an expr
-- TODO: This type needs a better name 

-- The instance is a model, but has the same structure as an EqTheory 
type Instance = EqTheory 

mapAsFunc :: Rename -> RenameFunc
mapAsFunc r = \x -> Map.findWithDefault x x r

instantiate :: EqTheory -> Maybe Int -> Instance
instantiate eq (Just indx) =
  let a = args eq
      instNm = twoCharName (eq ^. thyName) indx
      renMap = map (\(PConstr nm _ _) -> (nm,nm ++ show indx)) a
      newdecls = gmap (mapAsFunc (Map.fromList renMap)) (decls eq) 
  in EqTheory instNm 
      (if (length a /= 0) then head newdecls else head a)
      (take (length $ eq ^. funcTypes) (drop 1 newdecls))
