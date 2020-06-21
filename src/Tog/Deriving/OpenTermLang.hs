module Tog.Deriving.OpenTermLang
  ( openLangNm,
    olangSuffix,
    varsConstrName, 
    openTermLang) where

import Tog.Deriving.EqTheory as Eq 
import Tog.Deriving.TUtils
import Tog.Deriving.Types (Name_)
import Tog.Raw.Abs
import Tog.Deriving.Utils.Renames
import Tog.Deriving.Types (gmap)

import Control.Lens ((^.))

varsConstrName :: String 
varsConstrName = "v"

openLangNm :: Eq.EqTheory -> Name_ 
openLangNm thy = thy ^. thyName ++ "OpenLang"

olangSuffix :: String
olangSuffix = "OL"

liftConstr :: Expr -> Expr 
liftConstr (App [arg]) = (App [arg,mkArg "n"])
liftConstr x = x -- error $ show x 

vars :: Name_ -> Constr 
vars langNm = 
  Constr (mkName varsConstrName) $
    (Fun (App [mkArg "Fin",mkArg "n"])
         (App [Arg $ App [mkArg langNm,mkArg "n"]]))

openTermLang :: Eq.EqTheory -> Decl
openTermLang eq =
 let nm = openLangNm eq
 in Data (mkName nm) (ParamDecl [Bind [mkArg "n"] (App [mkArg "Nat"])]) $ 
     DataDeclDef setType $ 
      (vars nm) : (gmap liftConstr $ applyRenames eq (nm,olangSuffix))

