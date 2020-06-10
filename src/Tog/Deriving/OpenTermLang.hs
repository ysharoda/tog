module Tog.Deriving.OpenTermLang (nat,fin,openTermLang) where

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

nat :: String 
nat =
  "data Nat : Set where { " ++ 
    "zero : Nat ; " ++ 
    "succ  : Nat -> Nat }"

fin :: String 
fin =
  "data Fin (n : Nat) : Set where { " ++
    "fzero : {m : Nat} (p : n == succ m) -> Fin n ; " ++
    "fsuc  : {m : Nat} (p : n == succ m) (i : Fin m) -> Fin n }"    

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
     -- constructors = gmap (ren (getConstrName $ eq^.Eq.sort) (nm,"OL")) $ eq^.Eq.funcTypes
 in Data (mkName nm) (ParamDecl [Bind [mkArg "n"] (App [mkArg "Nat"])]) $ 
     DataDeclDef setType $ 
      (vars nm) : (gmap liftConstr $ applyRenames eq (nm,"OL"))

