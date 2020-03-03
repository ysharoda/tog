module Tog.TUtils where

import Tog.Raw.Abs
import Tog.DerivingInsts()
-- import Tog.AbstractTypes
import qualified Data.Generics as Generics

type Name_ = String

noSrcLoc :: (Int,Int)
noSrcLoc = (0,0) 

homFuncName :: String 
homFuncName = "hom"

createId :: String -> Expr
createId str = Id $ NotQual $ Name (noSrcLoc,str)

getNameAsStr :: Name -> Name_
getNameAsStr (Name (_,n)) = n 

mkName :: Name_ -> Name
mkName str = Name (noSrcLoc,str) 

mkConstructor :: Name_ -> Name
mkConstructor str = mkName $ str ++ "C" 

setType :: Name
setType = mkName "Set"

getConstrName :: Constr -> Name_
getConstrName (Constr n _) = getNameAsStr n 

getArgName :: Arg -> [Name_]
getArgName (Arg (Id (NotQual (Name (_,n))))) = [n]
--getArgName (Fun e1 e2) = 
  --Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n]) arg

getBindingArgNames :: Binding -> [Name_]
getBindingArgNames (Bind args _) =
  Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) args
getBindingArgNames (HBind args e) =
  getBindingArgNames (Bind args e)


-- for decl e of monoid instance M1, the output is (e M1) 
qualDecl :: Name_ -> Name_ -> Expr
qualDecl declName instName =
  App [Arg (createId $ declName), Arg (createId instName)]

notQualDecl :: Name_ -> Expr 
notQualDecl declName =
  App [Arg (createId $ declName)]

-- For Name Monoid and number 1, the output is M1 
genCharName :: Name_ -> Int -> Name_
genCharName declName num =
  (take 1 declName) ++ show num

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







  

{- ----- creating pres axioms ------- -}
{-

genBind :: Expr -> [Binding]
genBind expr =
  let args  = map (\x -> Arg $ createIdNQ x) $ genVars $ arity expr
      rename (Arg (Id (NotQual (Name (l,n))))) =
             (Arg (Id (NotQual (Name (l,n++suffix1)))))
      rename harg = error $ "Unexpected Pattern" ++ show harg 
      types e =
        case e of
          App arg   -> [App (map rename arg)]
          Fun e1 e2 -> (types e1) ++ (types e2)
          _         -> error "invalid expression"
   in zipWith (\v ty -> HBind [v] ty) args (types expr)

genHomFuncApp :: Constr -> Name -> Expr
genHomFuncApp constr inst =
  App $ [strToArg homFuncName] ++ genHomFuncArg constr inst

genHomFuncArg :: Constr -> Name -> [Arg]
genHomFuncArg (Constr name expr) inst =
  -- qualifying by the instance name  
  let funcName = App [strToArg (nameToStr name), strToArg (nameToStr inst)] 
      vars  = map (\x -> createIdNQ x) $ genVars $ arity expr
   in case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> map Arg $ funcName:vars
       Fun _ _  -> [Arg $ App $ map Arg $ funcName:vars]
       x -> error $ "Invalid expr " ++ show x

genLHS :: Constr -> Name -> Expr
genLHS constr inst = genHomFuncApp constr inst

genRHS :: Constr -> Name -> Expr
genRHS (Constr name expr) inst =
  let funcName = App [strToArg (nameToStr name), strToArg (nameToStr inst)]
      vars  = map (\x -> createIdNQ x) $ genVars $ arity expr
      args (Id qname) = genHomFuncApp (Constr (Name ((6,6),"dummy")) (Id qname)) inst
      args x =  error $ "Invalid expr " ++ show x
--      args (App [Arg a]) = args a
--      args (App (a:as)) = args (App [a]) ++ (args $ App as)
--      args (Fun e1 e2)  = args e1 ++ args e2  
  in App $ map Arg $ funcName:(map args vars)

genEq :: Constr -> Expr
genEq constr =
  let inst1 = Name ((7,7),instanceName ++ suffix1)
      inst2 = Name ((8,8),instanceName ++ suffix2)
  in  Eq (genLHS constr inst1)
         (genRHS constr inst2)

createPresAxioms :: Constr -> Constr
createPresAxioms c@(Constr (Name (_,op)) e) =
  let name = "pres-" ++ op
      binding = genBind e
      -- vars = map (\x -> Arg $ createNotQualId x) $ genVars $ arity expr
  in Constr (Name (loc,name))
            (Pi (Tel binding) (genEq c)) 
-}
