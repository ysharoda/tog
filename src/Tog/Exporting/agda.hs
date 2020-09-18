 {-# LANGUAGE UnicodeSyntax #-}

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
  printAgda (Qual qn n) = printAgda qn <> dot <> printAgda n
  printAgda (NotQual n) = printAgda n 

instance PrintAgda Constr where 
  printAgda (Constr nm typ) =
    printAgda nm <+> text ofType <+> printAgda typ

instance PrintAgda Arg where
  printAgda arg = printAgda (getArgExpr arg) 

instance PrintAgda Binding where
  printAgda b =
    let arguments as = foldr (<+>) empty (map printAgda as)
        binding x =  arguments (getBindingArgs x) <+> text ofType <+> printAgda (getBindingExpr x) 
    in case b of
      Bind  _ _ -> parens $ binding b
      HBind _ _ -> braces $ binding b 

instance PrintAgda [Binding] where
  printAgda bindsList =
    encloseSep empty empty (text pi_representation) $ map printAgda bindsList

instance PrintAgda Telescope where
  printAgda (Tel binds) = printAgda binds 

instance PrintAgda Expr where
  printAgda (Lam names expr) =
    text lambda <+>
    foldr (<+>) empty (map printAgda names) <+> 
    text lambdaArrow <+>
    printAgda expr
  printAgda (Pi tel expr) =
    printAgda tel <+> text (pi_representation) <+> printAgda expr
  printAgda (Fun e1 e2) =
    printAgda e1 <+> text fun_sep <+> printAgda e2
  printAgda (Eq e1 e2) = -- might need to have a bracket here 
    printAgda e1 <+> text equality_symbol <+> printAgda e2
  printAgda (App args) =
    let pr = foldr (<+>) empty (map printAgda args)
    in if length args == 1 then pr else parens pr     
  printAgda (Id qname) = printAgda qname

instance PrintAgda Fields where
  printAgda NoFields = empty
  printAgda (Fields constrs) = vsep $ map printAgda constrs

instance PrintAgda Params where
  printAgda (ParamDecl binds) = printAgda binds
  printAgda _ = empty 

instance PrintAgda RecordBody where
  printAgda (RecordDecl typ) = recordHeader typ 
  printAgda (RecordDef typ flds) = recordHeader typ <$$> recordFields flds 
  printAgda (RecordDeclDef typ constructor flds) =
    recordHeader typ <$$> recordConstructor constructor <$$> recordFields flds

instance PrintAgda Decl where
  printAgda (Record nm params body) =
    (text record_keyword) <+> printAgda nm <+> printAgda params <+> printAgda body
  printAgda _ = empty 

-- Utils functions --
-- nm is the type "Set" 
recordHeader :: Name -> Doc
recordHeader nm = text ofType <+> printAgda nm <+> text record_beforeDecls

-- nm is the constructor name 
recordConstructor :: Name -> Doc
recordConstructor nm = indent 2 $ text record_constructor <+> printAgda nm

recordFields :: Fields -> Doc
recordFields flds = indent 2 $ text record_beforeFlds <$$> (indent 2 $ printAgda flds)
    

-- the config that needs to be imported --
ofType, lambda, lambdaArrow, pi_representation, fun_sep, equality_symbol, record_keyword, record_beforeDecls, record_constructor, record_beforeFlds :: String 
ofType = ":"
lambda = "\\"
lambdaArrow = "->"
pi_representation = "->"
fun_sep = "->"
equality_import = "import Relation.Binary.PropositionalEquality" 
equality_symbol = "≡"
record_keyword = "record"
record_beforeDecls = "where" 
record_constructor = "constructor"
record_beforeFlds = "fields" 
