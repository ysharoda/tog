module Tog.Deriving.OpenTermLang where

import Tog.Deriving.EqTheory as Eq 
import Tog.Deriving.TUtils
import Tog.Deriving.Types (Name_, gmap)
import Tog.Raw.Abs
import Tog.Parse (parseDecl)
import Tog.Deriving.Utils.Names (ren) 

import Control.Lens ((^.))

varsConstrName :: String 
varsConstrName = "v"

openLangNm :: Eq.EqTheory -> Name_ 
openLangNm thy = thy ^. thyName ++ "OpenLang"

fin :: String 
fin =
  "data Fin (n : Nat) : Set where { " ++
    "fzero : {m : Nat} (p : n == succ m) -> Fin n ; " ++
    "fsuc  : {m : Nat} (p : n == succ m) (i : Fin m) -> Fin n }"    

nat :: String 
nat =
  "data Nat : Set where { " ++ 
    "zero : Nat ; " ++ 
    "succ  : Nat -> Nat }"

strToDecl :: String -> Decl
strToDecl str =
  case parseDecl str of 
    Left _  -> error $ "invalide declaration " ++ str 
    Right r -> r 

vars :: Name_ -> Constr 
vars langNm = 
  Constr (mkName varsConstrName) $
    Pi (Tel [HBind [mkArg "n"] (App [mkArg "Nat"])])
       (Fun (App [mkArg "Fin",mkArg "n"])
            (App [mkArg langNm]))

openTermLang :: Eq.EqTheory -> Decl
openTermLang eq =
 let nm = openLangNm eq
     constructors = gmap (ren (getConstrName $ eq^.Eq.sort) (nm,"OL")) $ eq^.Eq.funcTypes
 in Data (mkName nm) NoParams $ 
     DataDeclDef setType
      ((vars nm) : constructors) 

