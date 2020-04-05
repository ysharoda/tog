module Tog.Deriving.TUtils
  ( getConstrName
  , mkName
  , setType
  , mkField
  , shortName
  , createThryInstType
  , qualDecl, notQualDecl
  , genVars
  , getArgName
  , exprArity
  , getBindingArgNames
  , mkArg
  , fldsToBinding
  ) where

import qualified Data.Generics as Generics
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

getArgName :: Arg -> [Name_]
getArgName (Arg (Id (NotQual (Name (_,n))))) = [n]
getArgName _ = error "Not an identifier"

getBindingArgNames :: Binding -> [Name_]
getBindingArgNames (Bind args _) =
  Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) args
getBindingArgNames (HBind args e) =
  getBindingArgNames (Bind args e)

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
genVars i = zipWith (++) (take i $ repeat "x") $ map show [1..i]

-- creates something like (M1 : Monoid A1)  
createThryInstType :: Name_ -> [Constr] -> Int -> Expr 
createThryInstType thryName thryParams index =
  App $ [mkArg thryName] ++
        map (\constr -> mkArg $ (getConstrName constr) ++ show index) thryParams

mkField :: [Constr] -> Fields
mkField [] = NoFields 
mkField xs = Fields xs

fldsToBinding :: Constr -> Binding
fldsToBinding (Constr nm typ) = Bind [mkArg $ nm^.name] typ 

