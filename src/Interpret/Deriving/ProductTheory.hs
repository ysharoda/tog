module Interpret.Deriving.ProductTheory
  ( prodTheoryToDecl
  , productThry
  ) where

import           Control.Lens ((^.), over, set)

import           Tog.Raw.Abs
import           Interpret.Utils.TUtils
import           Interpret.Flattener.Types (gmap)
import qualified Interpret.Deriving.EqTheory as Eq
import           Interpret.Utils.Renames (simpleRen)

-- There is no need for a new data-structure!
productThry :: Eq.EqTheory -> Eq.EqTheory
productThry t =
  let -- apply renames to avoid the shadowing problem of Tog
      sortName = getConstrName (t' ^. Eq.sort) 
      t' = gmap (simpleRen "P" (Eq.args t)) t
      mkProd = productField sortName
  in 
   set  Eq.thyName ("Product") $
   over Eq.funcTypes (map mkProd) $
   over Eq.axioms (map mkProd)
   t'

prodTyp :: Name_ -> Expr
prodTyp nm = let n = mkArg nm in App [mkArg "Prod", n, n]

productField :: Name_ -> Constr -> Constr
productField origSort constr =
  let adjustSort expr@(App [a]) = 
        if srt == origSort then prodTyp srt else expr where srt = getArgName a
      adjustSort x = x  
  in gmap adjustSort constr

prodTheoryToDecl :: Eq.EqTheory -> Decl
prodTheoryToDecl = Eq.toDecl (++ "C")
