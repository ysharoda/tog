module Tog.Deriving.TermLang
  ( termLang
  , termLangToDecl
  ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs (Constr, Name, Decl(Data), Params(NoParams), 
  DataBody(DataDeclDef))
import           Tog.Deriving.TUtils (mkName, getConstrName, setType)
import           Tog.Deriving.Types (Name_, gmap)
import           Tog.Deriving.Lenses (name)
import qualified Tog.Deriving.EqTheory as Eq

-- skip record as the projectors are not used
data TermLang = TermLang Name_ [Constr]

lang :: Eq.EqTheory -> Name_
lang t = Eq.thryName t ++ "Lang"

ren :: String -> Eq.EqTheory -> Name -> Name
ren sn thy n = mkName $ if (nam == sn) then lang thy else nam ++ "L"
  where nam = n^.name

termLang :: Eq.EqTheory -> TermLang
termLang t = TermLang (lang t) $ gmap r $ Eq.funcTypes t   
  where r = ren (getConstrName $ Eq.sort t) t

termLangToDecl :: TermLang -> Decl 
termLangToDecl (TermLang nm cs) =
  Data (mkName nm) NoParams $ DataDeclDef setType cs

