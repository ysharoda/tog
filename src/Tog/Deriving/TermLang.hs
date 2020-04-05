module Tog.Deriving.TermLang(termLang, termLangToDecl) where

import           Tog.Raw.Abs (Constr, Name, Decl(Data), Params(NoParams), 
  DataBody(DataDeclDef))
import           Tog.Deriving.TUtils (mkName, getConstrName, setType, name_)
import           Tog.Deriving.Types (Name_, gmap)
import qualified Tog.Deriving.EqTheory as Eq

-- skip record as the projectors are not used
data TermLang = TermLang Name_ [Constr]

name :: Eq.EqTheory -> Name_
name t = Eq.thryName t ++ "Lang"

ren :: String -> Eq.EqTheory -> Name -> Name
ren sn thy n = mkName $ if (nam == sn) then name thy else nam ++ "L"
  where nam = name_ n

termLang :: Eq.EqTheory -> TermLang
termLang t = TermLang (name t) $ gmap r $ Eq.funcTypes t   
  where r = ren (getConstrName $ Eq.sort t) t

termLangToDecl :: TermLang -> Decl 
termLangToDecl (TermLang nm cs) =
  Data (mkName nm) NoParams $ DataDeclDef setType cs

