module Tog.Deriving.TUtils
  ( getConstrName
  , mkName
  , mkQName 
  , setType
  , setTypeAsId
  , setTypeExpr
  , indexName
  , indexArg
  , mkField
  , shortName
  , twoCharName 
  , declTheory
  , qualDecl, notQualDecl
  , genVars
  , genVarsWSymb
  , getArgName
  , exprArity
  , mkArg
  , mkArg' 
  , mkFunc
  , fldsToBinding
  , fldsToHiddenBinds
  , mkParams
  , createId
  , strToDecl
  , eqFunArgs
  , eqFunApp
  , patternToExpr
  , getPatternName
  ) where

import Control.Lens ((^.))

import Tog.Raw.Abs
import Tog.DerivingInsts()
import Tog.Deriving.Types (Name_)
import Tog.Deriving.Lenses (name)
import Tog.Parse (parseDecl)

createId :: String -> Expr
createId = Id . NotQual . mkName

mkName :: Name_ -> Name
mkName str = Name ((1,20),str) 

mkQName :: Name_ -> QName
mkQName str = NotQual $ mkName str 

mkArg :: Name_ -> Arg
mkArg = Arg . createId

mkArg' :: Name_ -> Int -> Arg
mkArg' nam n = mkArg $ shortName nam n

setType :: Name
setType = mkName "Set"

setTypeExpr :: Expr
setTypeExpr = App [mkArg "Set"]

setTypeAsId :: Expr 
setTypeAsId = createId "Set" 

indexName :: Int -> Name -> Name
indexName i (Name (p,n)) = Name (p,n ++ show i)

indexArg :: Int -> Arg -> Arg
indexArg i a = mkArg $ (getArgName a) ++ show i 

getConstrName :: Constr -> Name_
getConstrName (Constr n _) = n ^. name

getArgName :: Arg -> Name_
getArgName (Arg (Id (NotQual (Name (_,n))))) = n
getArgName _ = error "Not an identifier"

qualDecl :: Name_ -> Name_ -> Expr
qualDecl declName instName = App [mkArg declName, mkArg instName]

notQualDecl :: Name_ -> Expr 
notQualDecl declName = App [mkArg declName]



mkFunc :: [Expr] -> Expr
mkFunc [] = error "cannot create function" 
mkFunc [x] = x 
mkFunc (x:xs) = Fun x (mkFunc xs) 

-- For Name Monoid and number 1, the output is M1 
shortName :: Name_ -> Int -> Name_
shortName declName num = take 1 declName ++ show num

-- using two characters for theory instance name to avoid name clashes with carriers.
twoCharName :: Name_ -> Int -> Name_
twoCharName declName num =
 let twocharNm = take 2 declName
 in if num == 0 then twocharNm else twocharNm ++ show num 

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
genVars i = genVarsWSymb 'x' i 

genVarsWSymb :: Char -> Int -> [String]
genVarsWSymb ch i = map (\z -> ch : show z)  [1..i]

-- creates something like (M1 : Monoid A1)  
declTheory :: Name_ -> [Constr] -> Int -> Expr 
declTheory n params index =
  if index == 0 then
    App $ mkArg n : map (\p -> mkArg $ getConstrName p) params
  else 
    App $ mkArg n : map (\p -> mkArg $ getConstrName p ++ show index) params

mkField :: [Constr] -> Fields
mkField [] = NoFields 
mkField xs = Fields xs

fldsToBinding :: Constr -> Binding
fldsToBinding (Constr nm typ) = Bind [mkArg $ nm^.name] typ

fldsToHiddenBinds :: Constr -> Binding
fldsToHiddenBinds (Constr nm typ) = HBind [mkArg $ nm^.name] typ 


mkParams :: [Binding] -> Params
mkParams [] = NoParams
mkParams ls = ParamDecl ls    

strToDecl :: String -> Decl
strToDecl str =
  case parseDecl str of 
    Left _  -> error $ "invalide declaration " ++ str 
    Right r -> r 

{-
data Expr
    = Lam [Name] Expr
    | Pi Telescope Expr
    | Fun Expr Expr
    | Eq Expr Expr
    | App [Arg]
    | Id QName
  deriving (Eq, Ord, Show, Read)
-} 

-- The input expression is the function type
-- The output expression is the function applied to variables 
eqFunArgs :: Expr -> [Arg]
eqFunArgs (Fun (App [a]) e2) = a : eqFunArgs e2
eqFunArgs (App args) = args
eqFunArgs _ = error "Something wrong" 

eqFunApp :: Constr -> Expr
eqFunApp (Constr nm (Fun e1 e2)) =
  App $ [mkArg (nm ^. name)] ++ eqFunArgs e1 ++ eqFunArgs e2
eqFunApp _ = error "not a function"

patternToExpr :: Pattern -> Expr
patternToExpr (IdP qname) = Id qname
patternToExpr (ConP qname ps) = App $ [Arg $ Id qname] ++ map (Arg . patternToExpr) ps
patternToExpr _ = error "either empty or hidden pattern"

getName :: QName -> String
getName (NotQual (Name (_,n))) = n
getName (Qual _ (Name (_,n))) = n 

getPatternName :: Pattern -> Name_
getPatternName (IdP qname) = getName qname
getPatternName (ConP qname _) = getName qname
getPatternName _ = error "either empty or hidden pattern"

