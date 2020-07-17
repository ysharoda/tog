module Tog.Deriving.Utils.Functions where

import Tog.Raw.Abs
import Tog.Deriving.Types  (Name_, gmap)
import Tog.Deriving.TUtils (mkName, mkQName, mkArg, genVars) 

import Tog.Deriving.Lenses (name)
import Control.Lens ((^.))

type FType = Constr

data FApp = FApp [Binding] Expr

getExpr :: FApp -> Expr 
getExpr (FApp _ e) = e 

farity :: Expr -> Int
farity e = farityH e -1
 where 
  farityH (Fun _ e2) = 1 + farityH e2
  farityH (App _) = 1
  farityH (Id _) = 1
  farityH (Pi (Tel bs) ex) = length bs + farityH ex
  farityH _ = error "not a function" 

class MkPattern a where
  mkPattern :: a -> Pattern

instance MkPattern FType where 
  mkPattern (Constr n typ) =
   let nm = n ^. name 
       arity = farity typ
       vars = genVars arity 
   in if (arity == 0)
        then IdP $ mkQName nm 
        else ConP (mkQName nm) $ map (IdP . mkQName) vars 

-- given an expression that is a function application (like op x y),
-- It returns a pattern to be used when pattern matching.  
instance MkPattern Expr where
  mkPattern (Id qn) = IdP qn
  mkPattern (App ars) =
   let qname (Arg (Id qn)) = qn
       qname _ = error "unknown pattern"
   in case ars of
    [Arg (Id x)] -> IdP x -- the case of a constant 
    [Arg (App (a:as))] -> -- the case of function application 
      ConP (qname a) (map (\(Arg x)  -> mkPattern x) as)  
    (a:as) -> ConP (qname a) (map (\(Arg x)  -> mkPattern x) as) -- nested function applicaions
    _ -> error "unknown pattern"
  mkPattern _ = error "unknown pattern"   

-- Given a func type, like (op : A -> A -> A), it returns an expr (op x1 x2) 
fapp :: FType -> FApp
fapp (Constr n typ) =
 let nm = n ^. name
     arity = farity typ
     vars = genVars arity
     etyp (Fun e _) = e -- this works because we are in unisorted setup
     etyp (App args) = App args
     etyp _ = error "not a function"
 in if (arity == 0) then FApp [] $ App [mkArg nm]
    else FApp [HBind (map mkArg vars) (etyp typ)]$
          App $ mkArg nm : map mkArg vars         

fappExpr :: FType -> Expr
fappExpr c = getExpr $ fapp c
{-  let (FApp b (App $ a:as)) = fapp c
  in case b of
    [Bind binds e] = App $ [a] ++ (take (length as) $ repeat (mkArg "_")) ++ as
    
  getExpr $ fapp c
-}
-- given an expression that is a function application (like op x y)
-- it maps a unary function to every argument of the function (like: op (f x) (f y)) 
functor :: Name_ -> Expr -> Expr
functor fnm (Id (NotQual (Name (_,n)))) = App [mkArg fnm, mkArg n]
functor fnm (App (a:as)) = App $ a : map (\x -> Arg $ App [mkArg fnm,x]) as
functor _ _ = error "invalid function application" 
-- QQ: Can we do better than passsing the name?
-- i.e.: pass a unary function (Expr -> Expr) 

functor' :: Expr -> Expr -> Expr
functor' (App args) (Id (NotQual (Name (_,n)))) = App (args ++ [mkArg n])
functor' (App args) (App (a:as)) = App $ a : (map (\x -> Arg $ App (args ++ [x])) as)
functor' _ _ = error "invalid function application" 


-- Given a type constructor C and a type A, it returns the type C A. 
liftType :: Name_ -> Arg -> Arg
liftType tconstr typ =
  Arg $ App [mkArg tconstr, typ] 

liftType' :: Name_ -> [Arg] -> Arg
liftType' tconstr types =
  Arg $ App $ mkArg tconstr : types

liftExprType :: Expr -> Arg -> Arg
liftExprType expr typ =
  Arg $ App $ (Arg expr) : [typ] 

-- 
liftConstr :: Name_ -> Constr -> Constr
liftConstr tconstr c =
  gmap (liftType tconstr) c 

curry' :: [Arg] -> Expr
curry' [x] = App [x]
curry' (x:xs) = Fun (App [x]) (curry' xs)
curry' _ = error "no args passed"

curryExpr :: [Expr] -> Expr
curryExpr [e] = e
curryExpr (e:es) = Fun e (curryExpr es)
curryExpr _ = error "not a valid expression"

mkSimpTypeSig :: Name_ -> [Arg] -> TypeSig
mkSimpTypeSig fname args =
  Sig (mkName fname) (curry' args) 

mkPiTypeSig :: Name_ -> [Binding] -> [Arg] -> TypeSig
mkPiTypeSig fname [] args = mkSimpTypeSig fname args
mkPiTypeSig fname binds args =
  Sig (mkName fname) (Pi (Tel binds) (curry' args)) 

mkFunDef :: Expr -> FunDefBody
mkFunDef e = FunDefBody e NoWhere 
