{-# LANGUAGE TemplateHaskell #-}
module Interpret.Deriving.EqTheory
  ( EqTheory
  , EqInstance
  , thyName
  , waist
  , sort
  , funcTypes
  , axioms
  , args
  , params
  , toDecl
  , build
  , eqInstance
  , projectConstr
  , applyProjConstr
  ) where 

import Data.Generics as Generics(Data)
import Control.Lens
import Data.List (isPrefixOf) 

import Tog.Raw.Abs   
import Interpret.Utils.TUtils (Name_, mkArg, mkParams, genVars, fldsToBinding, fldsToHiddenBinds, mkName, mkField, setType, twoCharName, genVarsWSymb)
import Interpret.Utils.Bindings
import Interpret.Utils.Functions 
import Interpret.Utils.Lenses (name)

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
  _waist      :: Int }
  deriving (Data)

makeLenses ''EqTheory

type EqInstance = (Name_,[Binding],Expr) 

decls :: EqTheory -> [Constr]
decls t = t^.sort : t^.funcTypes ++ t^.axioms

args :: EqTheory -> [Constr]
args t = take (t^.waist) $ decls t

params :: EqTheory -> Params
params = mkParams . map fldsToBinding . args

isArg :: EqTheory -> Constr -> Bool
isArg t c = c `elem` args t

toDecl :: (Name_ -> Name_) -> EqTheory -> Decl
toDecl ren t =
  let nm = t^.thyName in
  Record (mkName nm) (params t)
    (RecordDeclDef setType (mkName $ ren nm)
      (mkField $ drop (t^.waist) (decls t)))

build :: Name_ -> Constr -> [Constr] -> [Constr] -> Waist -> EqTheory
build = EqTheory

-- varName : The name of the variable representing the theory
-- Maybe Int : In case the application is indexed (mon A) or (Mon A1) 
eqInstance :: EqTheory -> Maybe Int -> EqInstance 
eqInstance thry indx =
  let iname i = twoCharName (thry ^. thyName) i 
      binds i =
        let bs = map fldsToHiddenBinds (args thry)
        in if i == 0 then bs else indexBindings i bs
      expr i =
        let bnames = getBindingsNames (binds i)
        in App $ mkArg (thry ^. thyName) : map mkArg bnames
   in case indx of
    Nothing -> (iname 0, binds 0, expr 0)
    Just i  -> (iname i, binds i, expr i)

-- called after checking that the constr is an argument   
findInBindings :: [Binding] -> Constr -> Name_
findInBindings binds (Constr n _) =
 case filter (isPrefixOf $ n ^. name) (getBindingsNames binds) of
   [] -> error "cannot locate argument"
   [a] -> a
   (a:_) -> a 

-- Given a theory, the name of an instance of the theory, and a constr,
-- the function returns the expression corresponding to the name of the operation
-- for example (op) or (op M1) 
projectConstr :: EqTheory -> EqInstance -> Constr -> Expr 
projectConstr thry (instName,binds,_) c@(Constr n _)  =
  if isArg thry c then App [mkArg $ findInBindings binds c]
  else App [mkArg (n ^. name),mkArg instName]


applyProjConstr :: EqTheory -> EqInstance -> Constr -> Maybe Char -> FApp
applyProjConstr thry i c@(Constr _ typ) varName =
  let ari = farity typ in
  if ari == 0 then ([], App [ Arg $ projectConstr thry i c ])
  else
    let vars = maybe genVars genVarsWSymb varName ari
        bindingsType = projectConstr thry i (thry ^. sort) 
    in  ([HBind (map mkArg vars) bindingsType],
        App $ (Arg $ projectConstr thry i c) : map mkArg vars) 
