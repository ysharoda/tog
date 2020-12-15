{-# OPTIONS_GHC -fno-warn-orphans #-}

module Tog.TimeTest.NFModule where

import Tog.Raw.Abs
import Control.DeepSeq

instance NFData Module where
  rnf (Module nm pars de) =
    rnf nm `seq` rnf pars `seq` rnf de

instance NFData Name where
  rnf (Name (_,nm)) = rnf nm

instance NFData QName where
  rnf (Qual qn n) = rnf qn `seq` rnf n
  rnf (NotQual n) = rnf n 

instance NFData Params where
  rnf (ParamDecl bs) = rnf bs
  rnf _ = () 

instance NFData Binding where
  rnf (Bind  args expr) = rnf args `seq` rnf expr
  rnf (HBind args expr) = rnf args `seq` rnf expr

instance NFData Arg where
  rnf (HArg e) = rnf e
  rnf (Arg  e) = rnf e 

instance NFData Expr where
  rnf (Lam ns e) = rnf ns `seq` rnf e
  rnf (Pi tel e) = rnf tel `seq` rnf e
  rnf (Fun e1 e2) = rnf e1 `seq` rnf e2
  rnf (Eq e1 e2) = rnf e1 `seq` rnf e2
  rnf (App as) = rnf as
  rnf (Id qn) = rnf qn 

instance NFData Telescope where
  rnf (Tel bs) = rnf bs 

instance NFData DeclOrLE where 
  rnf (Decl_ ds) = rnf ds
  rnf (Lang_ ls) = rnf ls 

instance NFData Decl where
  rnf (TypeSig ts) = rnf ts
  rnf (FunDef n ps body) = rnf n `seq` rnf ps `seq` rnf body
  rnf (Data n pars body) = rnf n `seq` rnf pars `seq` rnf body
  rnf (Record n pars body) = rnf n `seq` rnf pars `seq` rnf body
  rnf (Open qn) = rnf qn
  rnf (OpenImport imp) = rnf imp
  rnf (Import imp) = rnf imp
  rnf (Postulate ts) = rnf ts
  rnf (Module_ m) = rnf m

instance NFData Import where
  rnf (ImportNoArgs qn) = rnf qn 
  rnf (ImportArgs qn as) = rnf qn `seq` rnf as 

instance NFData Pattern where
  rnf (EmptyP _) = ()
  rnf (ConP qn ps) = rnf qn `seq` rnf ps
  rnf (IdP qn) = rnf qn
  rnf (HideP ps) = rnf ps 

instance NFData FunDefBody where
  rnf (FunDefNoBody) = ()
  rnf (FunDefBody e wh) = rnf e `seq` rnf wh

instance NFData Where where
  rnf NoWhere = ()
  rnf (Where ds) = rnf ds 

instance NFData DataBody where
  rnf (DataDecl n) = rnf n
  rnf (DataDef cs) = rnf cs
  rnf (DataDeclDef n cs) = rnf n `seq` rnf cs

instance NFData Constr where
  rnf (Constr n e) = rnf n `seq` rnf e 

instance NFData RecordBody where
  rnf (RecordDecl n) = rnf n
  rnf (RecordDef n fs) = rnf n `seq` rnf fs
  rnf (RecordDeclDef n t fs) = rnf n `seq` rnf t `seq` rnf fs

instance NFData Fields where
  rnf NoFields = ()
  rnf (Fields cs) = rnf cs 

instance NFData TypeSig where
  rnf (Sig n e) = rnf n `seq` rnf e 

instance NFData Language where
  rnf (TheoryC n cs)  = rnf n `seq` rnf cs
  rnf (MappingC n rs) = rnf n `seq` rnf rs
  rnf (ModExprC n me) = rnf n `seq` rnf me 

instance NFData RenPair where
  rnf (RenPair n1 n2) = rnf n1 `seq` rnf n2

instance NFData ModExpr where
  rnf (Extend n cs) = rnf n `seq` rnf cs
  rnf (Rename n rs) = rnf n `seq` rnf rs
  rnf (RenameUsing n1 n2) = rnf n1 `seq` rnf n2
  rnf (CombineOver n1 r1 n2 r2 n) = rnf n1 `seq` rnf r1 `seq` rnf n2 `seq` rnf r2 `seq` rnf n
  rnf (Combine n1 n2) = rnf n1 `seq` rnf n2
  rnf (Transport n1 n2) = rnf n1 `seq` rnf n2
  rnf (Arrow n1 n2) = rnf n1 `seq` rnf n2 

instance NFData Rens where
  rnf NoRens = ()
  rnf (Rens rs) = rnf rs
  rnf (NameRens n) = rnf n 
