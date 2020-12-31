-- Horribly named 'Utils' module that is a grab-bag of stuff
{-# LANGUAGE TemplateHaskell #-}
module Interpret.Utils.Utils 
  ( getParams
  , getFields
  , getBindingArgs
  , getBindingExpr
  , isFunc, isAxiom, isSort
  , checkParam
  ) where

import Tog.Raw.Abs 

isSort :: Expr -> Bool
isSort (Id (Qual _  (Name (_,"Set")))) = True
isSort (Id (NotQual (Name (_,"Set")))) = True
isSort (Lam _ e)  = isSort e
isSort (Pi _ e)   = isSort e
isSort (Fun e e') = isSort e && isSort e'
isSort (App args@((HArg _):_)) = and $ map (\(HArg a) -> isSort a) args
isSort (App args@((Arg  _):_)) = and $ map (\(Arg a) -> isSort a) args
isSort (Eq _ _) = False
isSort _ = False 

isFunc :: Expr -> Bool
isFunc (Id (NotQual (Name (_,"Set")))) = False
isFunc (Id (NotQual (Name (_,_))))     = True
isFunc (Id (Qual _  (Name (_,"Set")))) = False
isFunc (Id (Qual _  (Name (_,_))))     = True
isFunc (App args@((Arg  _):_))  = and $ map (\(Arg a)  -> isFunc a) args
isFunc (App args@((HArg  _):_)) = and $ map (\(HArg a) -> isFunc a) args
isFunc (Fun e1 e2) = isFunc e1 && isFunc e2
isFunc (Pi _ e)    = isFunc e
isFunc _ = False 

isAxiom :: Expr -> Bool
isAxiom (Eq _ _) = True
isAxiom (Lam _ e) = isAxiom e
isAxiom (Pi _ e)  = isAxiom e
isAxiom (Fun e e') = isAxiom e && isAxiom e'
isAxiom (App args@((HArg _):_)) = and $ map (\(HArg a) -> isAxiom a) args
isAxiom (App args@((Arg  _):_)) = and $ map (\(Arg a)  -> isAxiom a) args
isAxiom _ = False 

getBindingArgs :: Binding -> [Arg]
getBindingArgs (Bind  args _) = args
getBindingArgs (HBind args _) = args 

getBindingExpr :: Binding -> Expr
getBindingExpr (Bind  _ expr) = expr
getBindingExpr (HBind _ expr) = expr

checkParam :: (Expr -> Bool) -> Params -> Params
checkParam _ (NoParams) = NoParams
checkParam p (ParamDecl binds) =
  let sorts = [b | b <- binds, p (getBindingExpr b)]
  in if sorts == [] then NoParams else ParamDecl sorts 
checkParam _ _ = NoParams

{- ------------------------------------------------------------ -} 
{- ---------------------- Getters ----------------------------- -} 
{- ------------------------------------------------------------ -} 

-- makePrisms ''Arg
-- makePrisms ''Binding
-- makePrisms ''Expr

getParams :: Params -> [Binding]
getParams (ParamDecl bs) = bs
getParams _ = []

getFields :: Fields -> [Constr] 
getFields NoFields = []
getFields (Fields ls) = ls 
