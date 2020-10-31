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
  , eqInstance
  , projectConstr
  , applyProjConstr
  , mkPConstrs 
  ) where 

import Data.Generics as Generics(Data)
import Control.Lens

import Tog.Raw.Abs   
import Tog.Deriving.Types  (Name_)
import Tog.Deriving.TUtils (mkArg, mkParams, genVars, fldsToBinding, fldsToHiddenBinds, mkName, mkField, setType)
import Tog.Deriving.Utils.Bindings
import Tog.Deriving.Utils.Functions 
import Tog.Deriving.Utils.QualDecls
import Tog.Deriving.Lenses (name)

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
eqInstance :: EqTheory -> Maybe Int -> ([Binding],Expr) 
eqInstance thry Nothing =
  let binds  = map fldsToHiddenBinds (args thry)
      bnames = getBindingsNames binds
  in (binds, App $ mkArg (thry ^. thyName) : map mkArg bnames)
eqInstance thry (Just i) =
  let binds  = indexBindings True i $ map fldsToHiddenBinds (args thry)
      bnames = getBindingsNames binds
  in (binds, App $ mkArg (thry ^. thyName) : map mkArg bnames)   
  

-- Given a theory, the name of an instance of the theory, and a constr,
-- the function returns the expression corresponding to the name of the operation
-- for example (op) or (op M1) 
projectConstr :: EqTheory -> String -> Constr -> Expr 
projectConstr thry instName c@(Constr n _)  =
  if isArg thry c then App [mkArg (n ^. name)]
  else App [mkArg (n ^. name),mkArg instName]

applyProjConstr :: EqTheory -> String -> Constr -> Expr
applyProjConstr thry instName c@(Constr _ e) =
  let vars = genVars $ farity e 
  in App $ (Arg $ projectConstr thry instName c) : map mkArg vars 

mkPConstrs :: EqTheory -> (PConstr,[PConstr],[PConstr])
mkPConstrs t =
  let wst = t ^. waist
      axms  = t ^. axioms
      funcs = t ^. funcTypes
      constrs = (t ^. sort) : (funcs ++ axms)
      pconstrs = map (\(c,i) -> mkPConstr c wst i) $ zip  constrs [0..length constrs]
   in (head pconstrs,
       take (length funcs) (drop 1 pconstrs),
       take (length axms)  (drop (1 + length funcs) pconstrs)) 
