module Tog.Deriving.TermLang(termLang, termLangToDecl) where

import           Tog.Raw.Abs (Constr, Name(Name), Decl(Data), Params(NoParams), 
  DataBody(DataDeclDef))
import           Tog.Deriving.TUtils (Name_, mkName, getConstrName, setType)
import           Tog.Deriving.Types (gmap)
import qualified Tog.Deriving.EqTheory as Eq

-- skip record as the projectors are not used
data TermLang = TermLang Name_ [Constr]

mkLangName :: Eq.EqTheory -> Name_
mkLangName thry = Eq.thryName thry ++ "Lang"

ren :: String -> Eq.EqTheory -> Name -> Name
ren sn thy (Name (_,x)) = mkName $
  if (x == sn) then mkLangName thy
               else x++"L"

termLang :: Eq.EqTheory -> TermLang
termLang eqthry =
  let sortName = getConstrName $ Eq.sort eqthry
      r = ren sortName eqthry
  in  TermLang (mkLangName eqthry) $ gmap r $ Eq.funcTypes eqthry   

termLangToDecl :: TermLang -> Decl 
termLangToDecl (TermLang nm cs) =
  Data (mkName nm) NoParams $ DataDeclDef setType cs

