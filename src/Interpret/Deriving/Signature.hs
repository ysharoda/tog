module Interpret.Deriving.Signature 
  ( signature_
  , sigToDecl
  ) where

import Tog.Raw.Abs
import Interpret.Deriving.EqTheory as Eq
import Interpret.Utils.TUtils
import Interpret.Flattener.Types    (gmap)
import Interpret.Utils.Lenses   (name)

import Control.Lens ((^.), set)

ren :: Name -> Name
ren n = mkName $ if nam == "Set" then nam else nam ++ "S"
  where nam = n^.name


signature_ :: Eq.EqTheory -> Eq.EqTheory
signature_ = set Eq.thyName ("Sig") . set Eq.axioms [] .  gmap ren 

sigToDecl :: Eq.EqTheory -> Decl
sigToDecl = Eq.toDecl (++ "SigC")
