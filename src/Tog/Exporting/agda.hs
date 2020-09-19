 {-# LANGUAGE UnicodeSyntax #-}

module Tog.Exporting.Agda where

import Tog.Raw.Abs
import Tog.Deriving.Lenses (name)
import Tog.Deriving.Utils.Bindings (getBindingArgs, getBindingExpr)
import Tog.Deriving.TUtils (getArgExpr) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen as PP 

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
   foldr (<+>) empty $ map printAgda bindsList 
   -- encloseSep empty empty (text pi_representation) $ map printAgda bindsList

instance PrintAgda [Constr] where
  printAgda constrsList = vsep $ map printAgda constrsList   

instance PrintAgda Telescope where
  printAgda (Tel binds) = printAgda binds 

instance PrintAgda Expr where
  printAgda (Lam names expr) =
    text lambda <+>
    foldr (<+>) empty (map printAgda names) <+> 
    text lambdaArrow <+>
    printAgda expr
  printAgda (Pi tel expr) =
    printAgda tel <+> (if emptyTel tel then empty else text pi_representation) <+> printAgda expr
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
  printAgda (Fields constrs) = printAgda constrs 

instance PrintAgda Params where
  printAgda (ParamDecl binds) = printAgda binds
  printAgda _ = empty 

instance PrintAgda RecordBody where
  printAgda (RecordDecl typ) = recordHeader typ 
  printAgda (RecordDef typ flds) = recordHeader typ PP.<$> recordFields flds 
  printAgda (RecordDeclDef typ constructor flds) =
    recordHeader typ PP.<$> recordConstructor constructor PP.<$> recordFields flds

instance PrintAgda DataBody where
  printAgda (DataDecl nm) = dataHeader nm 
  printAgda (DataDef constrs) = printAgda constrs
  printAgda (DataDeclDef nm constrs) =
    dataHeader nm PP.<$> (indent 2 $ printAgda constrs) 

instance PrintAgda TypeSig where
  printAgda (Sig nm e) =
    printAgda nm <+> text ofType <+> printAgda e

instance PrintAgda Where where
  printAgda NoWhere = empty
  printAgda (Where decls) = text "where" <+> (vsep $ map printAgda decls) 

instance PrintAgda FunDefBody where
  printAgda FunDefNoBody = empty
  printAgda (FunDefBody e wher) = printAgda e PP.<$> printAgda wher

instance PrintAgda Pattern where
  printAgda (EmptyP _) = empty
  printAgda (ConP qnm ptrns) = parens $ printAgda qnm <+> (foldr (<+>) empty $ map printAgda ptrns)
  printAgda (IdP qnm) = printAgda qnm
  printAgda (HideP ptrn) = braces $ printAgda ptrn 

instance PrintAgda Import where
  printAgda (ImportNoArgs qn) = printAgda qn
  printAgda (ImportArgs qn args) = printAgda qn <+> (foldr (<+>) empty $ map printAgda args) 

instance PrintAgda Decl where
  printAgda (TypeSig typ) = printAgda typ
  printAgda (FunDef nm patterns body) =
    printAgda nm <+> (foldr (<+>) empty $ map printAgda patterns) <+> text fundef <+> printAgda body 
  printAgda (Data nm params body) =
    (text type_keyword) <+> printAgda nm <+> printAgda params <+> printAgda body  
  printAgda (Record nm params body) =
    (text record_keyword) <+> printAgda nm <+> printAgda params <+> printAgda body
  printAgda (Open imp) = text open <+> printAgda imp
  printAgda (Import imp) = text import_ <+> printAgda imp
  printAgda (OpenImport imp) = text open_import <+> printAgda imp
  printAgda (Module_ m) = printAgda m
  printAgda _ = empty

instance PrintAgda DeclOrLE where
  printAgda (Decl_ decls) = vsep $ map printAgda decls
  printAgda (Lang_ _) = error "theory expressions not accepted by Agda" 

instance PrintAgda Module where
  printAgda (Module nm params decls) =
    text module_ <+> printAgda nm <+>
    printAgda params <+> text module_beforeDecls PP.<$>
    (indent 2 $ printAgda decls)

-- Utils functions --
emptyTel :: Telescope -> Bool
emptyTel (Tel b) = null b 

-- nm is the type "Set" 
recordHeader :: Name -> Doc
recordHeader nm = text ofType <+> printAgda nm <+> text record_beforeDecls

-- nm is the constructor name 
recordConstructor :: Name -> Doc
recordConstructor nm = indent 2 $ text record_constructor <+> printAgda nm

recordFields :: Fields -> Doc
recordFields NoFields = empty
recordFields (Fields []) = empty 
recordFields flds =
  indent 2 $ text record_beforeFlds <$$> (indent 2 $ printAgda flds)

dataHeader ∷ Name → Doc
dataHeader nm = text ofType <+> printAgda nm <+> text type_beforeDecls

-- the config that needs to be imported --
ofType, lambda, lambdaArrow, pi_representation, fun_sep, equality_symbol, record_keyword, record_beforeDecls, record_constructor, record_beforeFlds :: String 
ofType = ":"
lambda = "λ"
lambdaArrow = "→"
pi_representation = "→"
fun_sep = "→"
equality_import = "import Relation.Binary.PropositionalEquality" 
equality_symbol = "≡"
record_keyword = "record"
record_beforeDecls = "where" 
record_constructor = "constructor"
record_beforeFlds = "field"
type_keyword = "data"
type_beforeDecls = "where" 
fundef = "="
open = "open"
open_import = "open import"
import_ = "import"
module_ = "module"
module_beforeDecls = "where" 
