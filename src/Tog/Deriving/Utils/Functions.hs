module Tog.Deriving.Utils.Functions where

import Tog.Raw.Abs
import Tog.Deriving.Types  (Name_, gmap)
import Tog.Deriving.TUtils (mkName, mkQName, mkArg, exprArity, genVars) 

import Tog.Deriving.Lenses (name)
import Control.Lens ((^.))

type FType = Constr

type FApp = Expr

class MkPattern a where
  mkPattern :: a -> Pattern

instance MkPattern FType where 
  mkPattern (Constr n typ) =
   let nm = n ^. name 
       arity = exprArity typ
       vars = genVars arity 
   in if (arity == 0)
        then IdP $ mkQName nm 
        else ConP (mkQName nm) $ map (IdP . mkQName) vars 

-- given an expression that is a function application (like op x y),
-- It returns a pattern to be used when pattern matching.  
instance MkPattern FApp where
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
     arity = exprArity typ
     vars = genVars arity
 in if (arity == 0) then App [mkArg nm]
    else App $ mkArg nm : map mkArg vars 
  
-- given an expression that is a function application (like op x y)
-- it maps a unary function to every argument of the function (like: op (f x) (f y)) 
functor :: Name_ -> FApp -> FApp
functor fnm (Id (NotQual (Name (_,n)))) = App [mkArg fnm, mkArg n]
functor fnm (App (a:as)) = App $ a : map (\x -> Arg $ App [mkArg fnm,x]) as
functor _ _ = error "invalid function application" 
-- QQ: Can we do better than passsing the name?
-- i.e.: pass a unary function (Expr -> Expr) 

-- Given a type constructor C and a type A, it returns the type C A. 
liftType :: Name_ -> Arg -> Arg
liftType tconstr typ =
  Arg $ App [mkArg tconstr, typ] 

liftConstr :: Name_ -> Constr -> Constr
liftConstr tconstr c =
  gmap (liftType tconstr) c 

curry' :: [Arg] -> Expr
curry' [x] = App [x]
curry' (x:xs) = Fun (App [x]) (curry' xs)
curry' _ = error "no args passed"

mkSimpTypeSig :: Name_ -> [Arg] -> TypeSig
mkSimpTypeSig fname args =
  Sig (mkName fname) (curry' args) 

