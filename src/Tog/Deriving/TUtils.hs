module Tog.Deriving.TUtils where

import qualified Data.Generics as Generics

import           Tog.Raw.Abs
import           Tog.DerivingInsts()
import           Tog.Deriving.Types (Name_)

noSrcLoc :: (Int,Int)
noSrcLoc = (0,0) 

homFuncName :: String 
homFuncName = "hom"

createId :: String -> Expr
createId str = Id $ NotQual $ Name (noSrcLoc,str)

name_ :: Name -> Name_
name_ (Name (_,n)) = n 

mkName :: Name_ -> Name
mkName str = Name (noSrcLoc,str) 

mkConstructor :: Name_ -> Name
mkConstructor str = mkName $ str ++ "C" 

setType :: Name
setType = mkName "Set"

getConstrName :: Constr -> Name_
getConstrName (Constr n _) = name_ n 

getArgName :: Arg -> [Name_]
getArgName (Arg (Id (NotQual (Name (_,n))))) = [n]
getArgName _ = error "Not an identifier"

getBindingArgNames :: Binding -> [Name_]
getBindingArgNames (Bind args _) =
  Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) args
getBindingArgNames (HBind args e) =
  getBindingArgNames (Bind args e)


-- for decl e of monoid instance M1, the output is (e M1) 
qualDecl :: Name_ -> Name_ -> Expr
qualDecl declName instName =
  App [Arg (createId declName), Arg (createId instName)]

notQualDecl :: Name_ -> Expr 
notQualDecl declName =
  App [Arg (createId $ declName)]

-- For Name Monoid and number 1, the output is M1 
shortName :: Name_ -> Int -> Name_
shortName declName num = take 1 declName ++ show num

createName :: Name_ -> Name
createName str = Name (noSrcLoc,str) 

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
  App $ [Arg $ createId thryName] ++
        map (\constr -> Arg $ createId $ (getConstrName constr) ++ show index) thryParams

mkField :: [Constr] -> Fields
mkField [] = NoFields 
mkField xs = Fields xs
