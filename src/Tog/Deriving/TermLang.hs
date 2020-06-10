module Tog.Deriving.TermLang
  ( termlangSuffix
  , termLang
  , termLangNm 
  ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs (Decl(Data), Params(NoParams),DataBody(DataDeclDef))
import           Tog.Deriving.TUtils (mkName, setType)
import           Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Utils.Renames (applyRenames)
import           Tog.Deriving.Types (Name_)

termlangSuffix :: String 
termlangSuffix = "L"

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
