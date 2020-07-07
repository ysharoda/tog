module Tog.Deriving.OpenTermLang
  ( openLangNm,
    olangSuffix,
    mapping, 
    openLangTyp,  
    varsConstrName, 
    openTermLang) where

import Tog.Deriving.EqTheory as Eq 
import Tog.Deriving.TUtils
import Tog.Deriving.Types (Name_)
import Tog.Raw.Abs
import Tog.Deriving.Utils.Renames
import Tog.Deriving.Types (gmap)
import Tog.Deriving.Lenses 

import Data.Map as Map (Map,fromList) 
import Control.Lens ((^.))

varsConstrName :: String 
varsConstrName = "v"

openLangNm :: Eq.EqTheory -> Name_ 
openLangNm thy = thy ^. thyName ++ "OpenLang"

openLangTyp :: Eq.EqTheory -> Expr
openLangTyp eq =
  Pi (Tel [HBind [mkArg "n"] (App [mkArg "Nat"])]) $
   (App [mkArg $ openLangNm eq, mkArg "n"]) 

olangSuffix :: String
olangSuffix = "OL"

mapping :: EqTheory -> Map Name_ Name_
mapping eq =
  let names = map (\(Constr n _) -> n ^. name) (eq ^. funcTypes) 
  in Map.fromList (zip names (map (++ olangSuffix) names)) 

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

