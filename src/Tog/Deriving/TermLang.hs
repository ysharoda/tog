module Tog.Deriving.TermLang
  ( termLang
  ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs (Decl(Data), Params(NoParams),DataBody(DataDeclDef))
import           Tog.Deriving.TUtils (mkName, getConstrName, setType)
import           Tog.Deriving.Types (Name_, gmap)
import           Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Utils.Names (ren) 

lang :: Eq.EqTheory -> Name_
lang t = t^.thyName ++ "Lang"

termLang :: Eq.EqTheory -> Decl
termLang t =
  let nm = lang t
      constructors = gmap (ren (getConstrName $ t^.Eq.sort) (nm,"L")) $ t^.Eq.funcTypes
  in Data (mkName $ lang t) NoParams $
      DataDeclDef setType constructors
