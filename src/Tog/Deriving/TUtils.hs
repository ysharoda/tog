module Tog.Deriving.TUtils
  ( getConstrName
  , mkName
  , setType
  , mkField
  , shortName
  , declTheory
  , qualDecl, notQualDecl
  , genVars
  , getArgName
  , exprArity
  , mkArg
  , fldsToBinding
  , mkParams
  ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs
import           Tog.DerivingInsts()
import           Tog.Deriving.Types (Name_)
import           Tog.Deriving.Lenses (name)

createId :: String -> Expr
createId = Id . NotQual . mkName

mkName :: Name_ -> Name
mkName str = Name ((0,0),str) 

setType :: Name
setType = mkName "Set"

getConstrName :: Constr -> Name_
getConstrName (Constr n _) = n ^. name

getArgName :: Arg -> Name_
getArgName (Arg (Id (NotQual (Name (_,n))))) = n
getArgName _ = error "Not an identifier"

qualDecl :: Name_ -> Name_ -> Expr
qualDecl declName instName = App [mkArg declName, mkArg instName]

notQualDecl :: Name_ -> Expr 
notQualDecl declName = App [mkArg declName]

mkArg :: Name_ -> Arg
mkArg = Arg . createId

-- For Name Monoid and number 1, the output is M1 
shortName :: Name_ -> Int -> Name_
shortName declName num = take 1 declName ++ show num

exprArity :: Expr -> Int
exprArity expr =
  let count e = 
       case e of
         Fun e1 e2      -> (count e1) + (count e2)
         App argslist   -> length argslist
         Id  _          -> 1
         Lam names _    -> length names
         Pi (Tel bs) e' -> length bs + count e'
         Eq  _  _       -> error "Not a function"
   in count expr -1

genVars :: Int -> [String] 
genVars i = map (\z -> 'x' : show z)  [1..i]

-- creates something like (M1 : Monoid A1)  
declTheory :: Name_ -> [Constr] -> Int -> Expr 
declTheory n params index =
  App $ mkArg n : map (\p -> mkArg $ getConstrName p ++ show index) params

mkField :: [Constr] -> Fields
mkField [] = NoFields 
mkField xs = Fields xs

fldsToBinding :: Constr -> Binding
fldsToBinding (Constr nm typ) = Bind [mkArg $ nm^.name] typ 

mkParams :: [Binding] -> Params
mkParams [] = NoParams
mkParams ls = ParamDecl ls    

