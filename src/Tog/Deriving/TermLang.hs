module Tog.Deriving.TermLang
  ( termLang
  ) where

import           Control.Lens ((^.))

import           Tog.Raw.Abs (Name, Decl(Data), Params(NoParams),
  DataBody(DataDeclDef))
import           Tog.Deriving.TUtils (mkName, getConstrName, setType)
import           Tog.Deriving.Types (Name_, gmap)
import           Tog.Deriving.Lenses (name)
import           Tog.Deriving.EqTheory as Eq

lang :: Eq.EqTheory -> Name_
lang t = t^.thyName ++ "Lang"

ren :: String -> String -> Name -> Name
ren sn newName n = mkName $ if (nam == sn) then newName else nam ++ "L"
  where nam = n^.name

termLang :: Eq.EqTheory -> Decl
termLang t =
  let nm = lang t
      cs = gmap (ren (getConstrName $ t^.Eq.sort) nm) $ t^.Eq.funcTypes
  in Data (mkName nm) NoParams $ DataDeclDef setType cs
