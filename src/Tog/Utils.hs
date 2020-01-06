module Tog.Utils where

import Tog.Raw.Abs 

isSort :: Expr -> Bool
isSort expr =
  case expr of 
    Id (Qual _  (Name (_,"Set"))) -> True
    Id (NotQual (Name (_,"Set"))) -> True
    Eq  _ _  -> False
    Lam _ e  -> isSort e
    Pi  _ e  -> isSort e
    Fun e e' -> isSort e && isSort e'
    App args@((HArg _):_) -> and $ map (\(HArg a) -> isSort a) args
    App args@((Arg  _):_)  -> and $ map (\(Arg a) -> isSort a) args
    _ -> False 

isFunc :: Expr -> Bool
isFunc expr =
  case expr of
    Id (NotQual (Name (_,"Set"))) -> False
    Id (NotQual (Name (_,_)))     -> True
    Id (Qual _  (Name (_,"Set"))) -> False
    Id (Qual _  (Name (_,_)))     -> True
    App args@((Arg  _):_)   -> and $ map (\(Arg a)  -> isFunc a) args
    App args@((HArg  _):_)  -> and $ map (\(HArg a) -> isFunc a) args
    Fun e1 e2 -> isFunc e1 && isFunc e2
    Pi  _ e   -> isFunc e
    _         -> False

isAxiom :: Expr -> Bool
isAxiom expr =
  case expr of
    Eq _ _  -> True
    Lam _ e -> isAxiom e
    Pi  _ e -> isAxiom e
    Fun e e' -> isAxiom e && isAxiom e'
    App args@((HArg _):_) -> and $ map (\(HArg a) -> isAxiom a) args
    App args@((Arg  _):_) -> and $ map (\(Arg a)  -> isAxiom a) args 
    _  -> False

{- QQ: Is there a predefined function that does that. Functor does not work here -} 
liftFilter :: (Expr -> Bool) -> [Constr] -> [Constr]
liftFilter _ [] = [] 
liftFilter p ((Constr n e):xs) =
  if p e then (Constr n e) : liftFilter p xs
         else  liftFilter p xs 

classify :: [Constr] -> ([Constr],[Constr],[Constr])
classify ls = (liftFilter isSort ls,
               liftFilter isFunc ls,
               liftFilter isAxiom ls)

nameToStr :: Name -> String
nameToStr (Name (_,n)) = n 

qnameToStr :: QName -> String
qnameToStr (NotQual name) = nameToStr name 
qnameToStr (Qual q  name) = qnameToStr q ++ "." ++ nameToStr name              

strToArg :: String -> Arg 
strToArg str = Arg $ createIdNQ str

nameStr :: Name -> String 
nameStr (Name (_,n)) = n 
