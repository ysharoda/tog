module Tog.Deriving.Signature 
  ( signature_
  , sigToDecl
  ) where

import           Control.Lens ((^.), over, set)

import Tog.Raw.Abs
import Tog.Deriving.EqTheory as Eq
import Tog.Deriving.TUtils
import Tog.Deriving.Types    (gmap)
import Tog.Deriving.Lenses   (name)

ren :: Name -> Name
ren n = mkName $ if nam == "Set" then nam else nam ++ "S"
  where nam = n^.name

signature_ :: Eq.EqTheory -> Eq.EqTheory
signature_ = over Eq.thyName (++ "Sig") . set Eq.axioms [] .  gmap ren

sigToDecl :: Eq.EqTheory -> Decl
sigToDecl = Eq.toDecl (++ "SigC")
