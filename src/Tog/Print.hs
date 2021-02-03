module Tog.Print where

import Tog.Raw.Abs
import Interpret.Utils.Lenses (name)
import Interpret.Utils.TUtils (getArgExpr)

import Text.PrettyPrint.Leijen
import Control.Lens ((^.))

class PrettyPrettyprint a where
  prettyprint :: a -> Doc

instance PrettyPrettyprint Name where
  prettyprint n = text $ n ^. name

instance PrettyPrettyprint QName where
  prettyprint (Qual qn n) = prettyprint qn <> dot <> prettyprint n
  prettyprint (NotQual n) = prettyprint n

instance PrettyPrettyprint Constr where
  prettyprint (Constr n e) = prettyprint n <+> text ":" <+> prettyprint e

instance PrettyPrettyprint Arg where
  prettyprint arg = prettyprint (getArgExpr arg)

instance PrettyPrettyprint Binding where
  prettyprint bind =
    case bind of
      Bind  as e  -> parens $ helper as e 
      HBind as e -> braces $ helper as e
    where helper as e = hsep (map prettyprint as) <+> text ":" <+> prettyprint e

instance PrettyPrettyprint [Binding] where
  prettyprint blist = hsep $ map prettyprint blist

instance PrettyPrettyprint [Constr] where
  prettyprint clist = vsep $ map prettyprint clist

instance PrettyPrettyprint Telescope where
  prettyprint (Tel binds) = prettyprint binds

instance PrettyPrettyprint Expr where
  prettyprint (Lam names e) =
    parens $ text "\\" <+> hsep (map prettyprint names) <+> text "->" <+> prettyprint e
  prettyprint (Pi tel e) =
    if emptyTel tel then prettyprint e
    else if hiddenHead tel then prettyprint tel <+> text "->" <+> prettyprint e
    else parens $ prettyprint tel <+> text "->" <+> prettyprint e
    where emptyTel (Tel b) = null b
          hiddenHead (Tel ((HBind _ _):_)) = True
          hiddenHead _ = False 
  prettyprint (Fun e1 e2) =
    parens $ prettyprint e1 <+> text "->" <+> prettyprint e2
  prettyprint (Eq e1 e2) =
    prettyprint e1 <+> text "==" <+> prettyprint e2
  prettyprint (App args) =
    if length args == 1 then hsep (map prettyprint args)
    else parens $ hsep (map prettyprint args)
  prettyprint (Id qn) = prettyprint qn

instance PrettyPrettyprint Fields where
  prettyprint NoFields = empty
  prettyprint (Fields cs) = prettyprint cs

instance PrettyPrettyprint Params where
  prettyprint (ParamDecl binds) = prettyprint binds
  prettyprint _ = empty

instance PrettyPrettyprint RecordBody where
  prettyprint (RecordDecl nm) = prettyprint nm <+> text "where" 
  prettyprint (RecordDef nm flds) =
    prettyprint nm <+> text "where" <$$> (indent 2 $ text "field" <$$> (indent 2 $ prettyprint flds))
  prettyprint (RecordDeclDef nm constr flds) =
    prettyprint nm <+> text "where" <$$> (indent 2 $ (text "constructor" <+> prettyprint constr)
                              <$$> text "field" <$$> (indent 2 $ prettyprint flds))

instance PrettyPrettyprint DataBody where
  prettyprint (DataDecl nm) = prettyprint nm <+> text "where" 
  prettyprint (DataDef cs) = text "where" <$$> (indent 2 $ (vsep $ map prettyprint cs))
  prettyprint (DataDeclDef nm cs) =
    prettyprint nm <+> text "where" <$$>
    (indent 2 $ vsep (map prettyprint cs))

instance PrettyPrettyprint TypeSig where
  prettyprint (Sig nm e) =
    prettyprint nm <+> text ":" <+> prettyprint e

instance PrettyPrettyprint Where where
  prettyprint NoWhere = empty
  prettyprint (Where decls) = text "where" <+> (vsep $ map prettyprint decls)

instance PrettyPrettyprint FunDefBody where
  prettyprint FunDefNoBody = empty
  prettyprint (FunDefBody e wher) = prettyprint e <+> prettyprint wher

instance PrettyPrettyprint Pattern where
  prettyprint (EmptyP _) = empty
  prettyprint (ConP qnm ptrns) = parens $ prettyprint qnm <+> (hsep $ map prettyprint ptrns)
  prettyprint (IdP qnm) = prettyprint qnm
  prettyprint (HideP ptrn) = braces $ prettyprint ptrn

instance PrettyPrettyprint Import where
  prettyprint (ImportNoArgs qn) = prettyprint qn
  prettyprint (ImportArgs qn args) = prettyprint qn <+> (hsep $ map prettyprint args)

instance PrettyPrettyprint Decl where
  prettyprint (TypeSig sig) = prettyprint sig
  prettyprint (FunDef nm ps body) = prettyprint nm <+> hsep (map prettyprint ps) <+> text "=" <+> prettyprint body
  prettyprint (Data nm ps body) =
    text "data" <+> prettyprint nm <+> prettyprint ps <+> text ":" <+> prettyprint body
  prettyprint (Record nm ps body) =
    text "record" <+> prettyprint nm <+> prettyprint ps <+> text ":" <+> prettyprint body 
  prettyprint (Open imp) = text "open" <+> prettyprint imp
  prettyprint (Import imp) = text "import" <+> prettyprint imp
  prettyprint (OpenImport imp) = text "open import" <+> prettyprint imp
  prettyprint (Module_ m) = prettyprint m
  prettyprint _ = empty

instance PrettyPrettyprint DeclOrLE where
  prettyprint (Decl_ decls) = vsep $ map prettyprint decls
  prettyprint (Lang_ _) = error "more modules need to be flattened."

instance PrettyPrettyprint Module where
  prettyprint (Module nm params decls) =
    text "module" <+> prettyprint nm <+> prettyprint params <+> text "where"
    <$$> (indent 2 $ prettyprint decls)
