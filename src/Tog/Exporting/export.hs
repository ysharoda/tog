 {-# LANGUAGE UnicodeSyntax #-}

module Tog.Exporting.Export where 

import Tog.Raw.Abs
import Tog.Deriving.Lenses (name)
import Tog.Deriving.Utils.Bindings (getBindingArgs, getBindingExpr)
import Tog.Deriving.TUtils (getArgExpr)

import Control.Lens ((^.))
import Data.List ((\\)) 
import Text.PrettyPrint.Leijen as PP

import Tog.Exporting.Config
import Tog.Exporting.Utils

class Export a where
  export :: Config -> a -> Doc

instance Export Name where
  export conf nm = text $ replace conf (nm ^. name)  

instance Export QName where 
  export conf (Qual qn n) = export conf qn <> dot <> export conf n
  export conf (NotQual n) = export conf n

instance Export Constr where
  export conf (Constr nm typ) = export conf nm <+> text (constr_oftype conf) <+> export conf typ

instance Export Arg where
  export conf arg = export conf (getArgExpr arg)

instance Export Binding where
  export conf binds =
    let arguments as = hsep $ map (export conf) as
        binding x =  arguments (getBindingArgs x) <+> text (bind_of_type conf) <+> export conf (getBindingExpr x)
    in case binds of
      Bind  _ _ -> parens $ binding binds
      HBind _ _ -> braces $ binding binds

instance Export [Binding] where
  export conf bindsList = hsep $ map (export conf) bindsList

instance Export [Constr] where
  export conf constrList = vsep $ map (export conf) constrList

instance Export Telescope where
  export conf (Tel binds) = export conf binds

emptyTel :: Telescope -> Bool
emptyTel (Tel b) = null b  

instance Export Expr where
  export conf (Lam names expr) =
   parens $ 
    text (lambda conf) <+>
    hsep (map (export conf) names) <+>
    text (fun_sep conf) <+>
    export conf expr
  export conf (Pi tel expr) =
   parens $ 
    if emptyTel tel then empty
    else text (before_constr_binds conf) <+> export conf tel <+> text (after_constr_binds conf) <+> export conf expr
  export conf (Fun e1 e2) =
    parens $ export conf e1 <+> text (fun_sep conf) <+> export conf e2
  export conf (Eq e1 e2) = 
    export conf e1 <+> text (equality conf) <+> export conf e2
  export conf (App args) =
    let App newargs = callFunc conf (App args)
        pr = hsep $ map (export conf) newargs
    in if length args == 1 then pr else parens pr
  export conf (Id qname) = export conf qname

instance Export Fields where
  export _     NoFields = empty
  export conf (Fields cs) = export conf cs

instance Export Params where
  export conf (ParamDecl binds) = export conf binds
  export _ _ = empty

instance Export RecordBody where
  export conf (RecordDecl _) = recordHeader conf Nothing
  export conf (RecordDef _ flds) = recordHeader conf (Just flds) <+> recordFields conf flds
  export conf (RecordDeclDef _ constructor flds) =
    recordHeader conf (Just flds) <+> recordConstructor conf constructor <+> recordFields conf flds

recordHeader :: Config ->  Maybe Fields -> Doc
recordHeader conf flds =
  universe <+> text (s4 conf isEmpty) <+> linebreak 
  where
    isEmpty = flds == Nothing || flds == Just NoFields || flds == Just (Fields [])
    universe = maybe (text (level0 conf)) (universeLevel conf) flds
  
-- nm is the constructor name
recordConstructor ::  Config -> Name -> Doc
recordConstructor conf nm =
  if printConstructors conf then text (s5 conf) <+> text (constructors conf) <+> export conf nm <+> text (s6 conf) <+> linebreak else empty 

recordFields ::  Config -> Fields -> Doc
recordFields _ NoFields = empty
recordFields _(Fields []) = empty
recordFields conf (Fields cs) =
  (if null (s7 conf) && null (fields conf) && null (s8 conf) then empty else text (s7 conf) <+> text (fields conf) <+> text (s8 conf) <+> linebreak)
  <+> (indent 2 $
         vsep $ map (printEnclose (s9 conf) (s10 conf) . export conf) cs) <+> linebreak    

instance Export DataBody where
  export conf (DataDecl nm) = dataHeader conf nm True 
  export conf (DataDef cs) = dataConstructors conf cs 
  export conf (DataDeclDef nm cs) =
    dataHeader conf nm (cs == []) <+> (indent 2 $ dataConstructors conf cs)

dataHeader ∷  Config -> Name -> Bool -> Doc
dataHeader conf nm isEmptyType = export conf nm <+> text (d4 conf isEmptyType) <+> linebreak

dataConstructors ::  Config -> [Constr] -> Doc
dataConstructors conf cs =
  (vsep $ map (printEnclose (d5 conf) (d6 conf) . export conf) cs) <+> linebreak    

instance Export TypeSig where
  export conf (Sig nm ex) =
   let p = export conf nm <+> text (f2 conf) <+> printExpr ex
       printExpr e =   
        case e of
          Pi tel expr -> 
            if emptyTel tel then text (f3 conf) <+> export conf expr <+> text (f4 conf) 
            else text (before_ftype_binds conf) <+> export conf tel <+> text (after_ftype_binds conf) <+> text (f3 conf) <+> export conf expr <+> text (f4 conf) 
              -- text f3 <+> text "Π" <+> export conf tel <+> text "," <+> export conf expr <+> text f4  
          expr -> text (f3 conf) <+> export conf expr
   in if (f1 conf == "") then p else text (f1 conf) <+> p
    
instance Export Where where
  export _ NoWhere = empty
  export conf (Where decls) = linebreak <+> text "where" <+> (vsep $ map (export conf) decls)

instance Export FunDefBody where
  export _ FunDefNoBody = empty
  export conf (FunDefBody e wher) = export conf e PP.<+> export conf wher

instance Export Pattern where
  export _    (EmptyP _) = empty
  export conf (ConP qnm ptrns) = parens $ export conf qnm <+> (hsep $ map (export conf) ptrns)
  export conf (IdP qnm) = export conf qnm
  export conf (HideP ptrn) = braces $ export conf ptrn

instance Export Import where
  export conf (ImportNoArgs qn) = export conf qn
  export conf (ImportArgs qn args) = export conf qn <+> (hsep $ map (export conf) args)
  

instance Export Decl where
  export conf (TypeSig sig) = export conf sig 
  export conf (FunDef nm ps body) =
    funcHeader (f5 conf) nm <+> (hsep $ map (export conf) ps) <+> text (f6 conf) <+> export conf body <+> text (f7 conf)
    where funcHeader flag fname = if flag =="fname" then export conf fname else text flag    
  export conf (Data nm ps body) =
    text (d1 conf) <+> export conf nm <+> text (d2 conf) <+> export conf ps <+> text (d3 conf) <+> export conf body <+> openDatatype conf nm
  export conf (Record nm ps body) =
    text (s1 conf) <+> export conf nm <+> text (s2 conf) <+> export conf ps <+> text (s3 conf) <+> export conf body 
  export conf (Open imp) = text (open_ conf) <+> export conf imp
  export conf (Import imp) = text (import_ conf) <+> export conf imp
  export conf (OpenImport imp) = text (openimport conf) <+> export conf imp
  export conf (Module_ m) =
    linebreak <+> export conf m  <+> linebreak -- to open the first declaration, which represents the equational theory.
  export _ _ = empty

instance Export DeclOrLE where
  export conf (Decl_ decls) = vsep $ map (export conf) $ preprocessDecls conf decls
  export _ (Lang_ _) = error "theory expressions not accepted by Agda"

instance Export Module where
  export conf (Module nm params (Decl_ decls)) =
    export conf (Decl_ imprts) <$$>
    text (m1 conf) <+> export conf nm <+> text (m2 conf) <+> 
    export conf params <+> text (m3 conf (decls == [])) PP.<$>
    (indent 2 $ export conf $ Decl_ defs) PP.<$>
    text (m4 conf) <+> (if module_end_has_name conf then export conf nm else empty)
    where imprts = if import_before_module conf then takeWhile isImport decls else [] 
          defs   = if import_before_module conf then decls \\ imprts else decls 
          isImport (Import _) = True
          isImport (Open _) = True
          isImport (OpenImport _) = True
          isImport _ = False
  export _ _ = error "theory expressions not accepted by Agda"
{-
imprts =
            if import_before_module conf then (Decl_ $ filter isImport decls, Decl_ $ decls \\ imprts)
            else (Decl_ [], d)
-} 
  
{- ---------- testing ---------- -}
{-
export conf :: Module -> IO () 
export conf file = do 
  s <- readFile file
  case parseModule s of
    Right (Module _ _ (Lang_ defs)) -> 
      putDoc $ export conf $ processDefs defs --  dirName mode (processDefs defs) (theories defs)
    Left err -> putDoc err   
    _ -> error "wrong file structure" 
-}
-- Utils functions --
printEnclose :: String -> String -> (Doc -> Doc) 
printEnclose prefix suffix =
  if prefix == "(" && suffix == ")" then parens 
  else (\x -> text prefix <+> x <+> text suffix)

openDatatype :: Config -> Name -> Doc 
openDatatype conf nm =
  if (open_datatypes conf) then text (open_ conf) <+> export conf nm <+> linebreak else empty     
