module Tog.Deriving.Utils.Bindings
  (indexOneBind,
   indexBindings, 
   repeatBinds,
   getOneBindNames,
   getBindingsNames,
   unionBindings,
   getBindingArgs,
   getBindingExpr,
   explicitBind,
   hiddenBind) where 

import Tog.Raw.Abs

import Tog.Deriving.Types (Name_)
import Tog.Deriving.TUtils
import Tog.Deriving.Types (gmap)

-- we need the isHidden flag, because we cannot infer if a function argument is hidden or not based on whether it is hidden or not in the datatype (eg: in the case of closed term langauge)  
indexOneBind :: Bool -> Int -> Binding -> Binding 
indexOneBind isHidden i (Bind  as e) =
 let newArgs =  map (indexArg i) as
 in if (isHidden) then HBind newArgs e else Bind newArgs e 
indexOneBind isHidden i (HBind as e) =
 let newArgs =  map (indexArg i) as
 in if (isHidden) then HBind newArgs e else Bind newArgs e

indexBindings :: Bool -> Int -> [Binding] -> [Binding]
indexBindings isHidden i binds = map (indexOneBind isHidden i) binds 

repeatBinds :: Int -> [Binding] -> [Binding]
repeatBinds 0 _ = [] 
repeatBinds 1 binds = binds
repeatBinds num binds =
  [indexOneBind True i b | b <- binds, i <- [1 .. num]]

getOneBindNames :: Binding -> [Name_]
getOneBindNames (Bind  as _) = map (\a -> getArgName a) as
getOneBindNames (HBind as _) = map (\a -> getArgName a) as

getBindingsNames :: [Binding] -> [Name_]
getBindingsNames binds = concatMap getOneBindNames binds

neutralizeBind :: Binding -> Binding
neutralizeBind b = gmap (\(Name ((_,_),n)) -> (Name ((0,0),n))) b 

alterBind :: Binding -> Binding
alterBind (Bind as e) = HBind as e
alterBind (HBind as e) = Bind as e

explicitBind :: Binding -> Binding
explicitBind (HBind as e) = Bind as e
explicitBind x = x

hiddenBind :: Binding -> Binding
hiddenBind (Bind as e) = HBind as e
hiddenBind x = x 

-- Problem: Deciding whether an argument should be hidden 
unionBindings :: [Binding] -> [Binding] -> [Binding]
unionBindings b1 [] = b1 
unionBindings b1 b2 =
  let nb1 = map neutralizeBind b1
      nb2 = map neutralizeBind b2
      b = head nb2 
  in if elem b nb1 || elem (alterBind b) nb1
     then unionBindings b1 (tail b2)
     else (unionBindings b1 (tail b2)) ++ [hiddenBind b]

getBindingArgs :: Binding -> [Arg]
getBindingArgs (Bind as _) = as
getBindingArgs (HBind as _) = as

getBindingExpr :: Binding -> Expr
getBindingExpr (Bind  _ expr) = expr
getBindingExpr (HBind _ expr) = expr
