module Tog.Deriving.TermLang
  ( mapping
  , termlangSuffix 
  , termLang
  , termLangNm 
  ) where

import Control.Lens ((^.))
import Data.Map as Map (Map,fromList) 

import Tog.Raw.Abs (Decl(Data), Params(NoParams),DataBody(DataDeclDef))
import Tog.Deriving.TUtils (mkName, setType)
import Tog.Deriving.EqTheory as Eq
import Tog.Deriving.Utils.Renames (applyRenames)
import Tog.Deriving.Types (Name_)
import Tog.Raw.Abs
import Tog.Deriving.Lenses (name)

termlangSuffix :: String 
termlangSuffix = "L"

mapping :: EqTheory -> Map Name_ Name_
mapping eq =
  let names = map (\(Constr n _) -> n ^. name) (eq ^. funcTypes) 
  in Map.fromList (zip names (map (++ termlangSuffix) names)) 

termLangNm :: Eq.EqTheory -> Name_
termLangNm eq =  eq^.thyName ++ "Lang"

termLang :: Eq.EqTheory -> Decl
termLang eq =
  let nm = termLangNm eq
      -- constructors = gmap (ren (getConstrName $ t^.Eq.sort) (nm,"L")) $ t^.Eq.funcTypes
  in Data (mkName nm) NoParams $
      DataDeclDef setType $ applyRenames eq (nm,termlangSuffix)

--getConstructors :: Decl -> [Constr]       
--getConstructors (Data n _ (DataDeclDef _ constructors)) = constructors 
