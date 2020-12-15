{-# OPTIONS_GHC -fno-warn-orphans #-}

module Tog.TimeTest.NFAModule where

import Tog.Abstract
import Tog.Names
import Control.DeepSeq

instance NFData Module where
  rnf (Module qn pars qns ds) =
    rnf qn `seq` rnf pars `seq` rnf qns `seq` rnf ds 

instance NFData SrcLoc where
  rnf (SrcLoc pl pc) = rnf pl `seq` rnf pc 

instance NFData Name where
  rnf (Name nloc nstr) = rnf nloc `seq` rnf nstr 
    
instance NFData QName where
  rnf (QName qn qnm) = rnf qn `seq` rnf qnm 

instance NFData Decl where
  rnf (TypeSig ts) = rnf ts
  rnf (Postulate ts) = rnf ts
  rnf (Data ts) = rnf ts
  rnf (Record ts) = rnf ts
  rnf (FunDef qn cls) = rnf qn `seq` rnf cls 
  rnf (DataDef qn ns ts) = rnf qn `seq` rnf ns `seq` rnf ts
  rnf (RecDef qn1 ns qn2 ts) = rnf qn1 `seq` rnf ns `seq` rnf qn2 `seq` rnf ts
  rnf (Module_ m) = rnf m
  rnf (Import qn es) = rnf qn `seq` rnf es
  rnf (Open qn) = rnf qn 
  
instance NFData TypeSig where
  rnf (Sig qn e) = rnf qn `seq` rnf e 

instance NFData Clause where
  rnf (Clause ps body) = rnf ps `seq` rnf body 

instance NFData Pattern where
  rnf (VarP n) = rnf n
  rnf (WildP srcloc) = rnf srcloc
  rnf (ConP qn ps) = rnf qn `seq` rnf ps
  rnf (EmptyP srcloc) = rnf srcloc 

instance NFData ClauseBody where
  rnf (ClauseNoBody) = ()
  rnf (ClauseBody e ds) = rnf e `seq` rnf ds 

instance NFData Expr where
  rnf (Lam n e) = rnf n `seq` rnf e
  rnf (Pi n e1 e2) = rnf n `seq` rnf e1 `seq` rnf e2
  rnf (Fun e1 e2) = rnf e1 `seq` rnf e2
  rnf (Equal e e1 e2) = rnf e `seq` rnf e1 `seq` rnf e2
  rnf (App hd els) = rnf hd `seq` rnf els
  rnf (Set srcloc) = rnf srcloc
  rnf (Meta srcloc) = rnf srcloc
  rnf (Refl srcloc) = rnf srcloc
  rnf (Con qn es) = rnf qn `seq` rnf es 

instance NFData Head where
  rnf (Var n) = rnf n
  rnf (Def qn) = rnf qn
  rnf (J srcloc) = rnf srcloc 
    
instance NFData Elim where
  rnf (Apply e) = rnf e
  rnf (Proj qn) = rnf qn 

    
