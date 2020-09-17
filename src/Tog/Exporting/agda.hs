module Agda where

import Tog.Raw.Abs
import Tog.Deriving.Lenses (name)
import Tog.Deriving.Utils.Bindings (getBindingArgs, getBindingExpr)
import Tog.Deriving.TUtils (getArgExpr) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen

class PrintAgda a where
  printAgda :: a -> Doc 

instance PrintAgda Name where
  printAgda nm =
    text (nm ^. name)

instance PrintAgda QName where
  printAgda (Qual qn n) = printAgda qn <> text "." <> printAgda n
  printAgda (NotQual n) = printAgda n 

instance PrintAgda Constr where 
  printAgda (Constr nm typ) =
    printAgda nm <+> text ofType <+> printAgda typ

instance PrintAgda Arg where
  printAgda arg = printAgda (getArgExpr arg) 

instance PrintAgda Binding where
  printAgda b =
    let arguments as = encloseSep empty empty (text " ") (map printAgda as)
        binding x =  arguments (getBindingArgs x) <+> text ofType <+> printAgda (getBindingExpr x) 
    in case b of
      Bind  _ _ -> parens $ binding b
      HBind _ _ -> braces $ binding b 

instance PrintAgda Telescope where
  printAgda (Tel binds) =
    encloseSep empty empty (text $ " " ++ pi_representation ++ " ") $ map printAgda binds

instance PrintAgda Expr where
  printAgda (Lam names expr) =
    text lambda <//>
    encloseSep empty empty (text " ") (map printAgda names) <//>
    text lambdaArrow <//>
    printAgda expr
  printAgda (Pi tel expr) =
    printAgda tel <//> text (pi_representation) <//> printAgda expr
  printAgda (Fun e1 e2) =
    printAgda e1 <//> text fun_sep <//> printAgda e2
  printAgda (Eq e1 e2) = -- might need to have a bracket here 
    printAgda e1 <+> text equality_symbol <+> printAgda e2
  printAgda (App args) =
    let pr = encloseSep empty empty (text " ") (map printAgda args)
    in if length args == 1 then pr else parens pr     
  printAgda (Id qname) = printAgda qname 
    
  

-- the config that needs to be imported --
ofType, lambda, lambdaArrow, pi_representation, fun_sep, equality_symbol :: String 
ofType = ":"
lambda = "\\"
lambdaArrow = "->"
pi_representation = "->"
fun_sep = "->"
equality_symbol = "==" 
