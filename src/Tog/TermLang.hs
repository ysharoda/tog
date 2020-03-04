module Tog.TermLang where

import Tog.Raw.Abs
import Tog.TUtils
import Tog.EqTheory
import qualified Data.Generics as Generics

data TermLang = TermLang {
  langName :: Name_ ,
  constructors :: [Constr] } 

mkLangName :: EqTheory -> Name_
mkLangName thry = getThryName thry ++ "Lang"

termLang :: EqTheory -> TermLang
termLang eqthry =
  let sortName = getConstrName $ getSort eqthry
      ren (Name (_,x)) = if (x == sortName) then mkName $ mkLangName eqthry else mkName $ x++"L"
  in  TermLang (mkLangName eqthry) $ Generics.everywhere (Generics.mkT ren) $ getFuncTypes eqthry   

termLangToDecl :: TermLang -> Decl 
termLangToDecl (TermLang nm cs) =
  Data (mkName nm) NoParams
       (DataDeclDef (mkName "Set") cs)

