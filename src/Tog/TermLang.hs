module Tog.TermLang where

import Tog.Raw.Abs
import Tog.TUtils
import qualified Tog.EqTheory as Eq
import qualified Data.Generics as Generics

data TermLang = TermLang {
  langName :: Name_ ,
  constructors :: [Constr] } 

mkLangName :: Eq.EqTheory -> Name_
mkLangName thry = Eq.thryName thry ++ "Lang"

termLang :: Eq.EqTheory -> TermLang
termLang eqthry =
  let sortName = getConstrName $ Eq.sort eqthry
      ren (Name (_,x)) = if (x == sortName) then mkName $ mkLangName eqthry else mkName $ x++"L"
  in  TermLang (mkLangName eqthry) $ Generics.everywhere (Generics.mkT ren) $ Eq.funcTypes eqthry   

termLangToDecl :: TermLang -> Decl 
termLangToDecl (TermLang nm cs) =
  Data (mkName nm) NoParams (DataDeclDef (mkName "Set") cs)

