module Interpret.Deriving.ProductTheory
  ( prodTheoryToDecl, productThry
  ) where

import           Control.Lens ((^.), set)

import           Tog.Raw.Abs
import           Interpret.Utils.TUtils
import           Interpret.Utils.Lenses (name)
import           Interpret.Flattener.Types (gmap)
import qualified Interpret.Deriving.EqTheory as Eq


ren :: Name_ -> Name -> Name
ren sortName n =
  mkName $
    if nam == "Set" then nam
    else if nam == sortName then nam
    else nam ++ "P"
  where nam = n^.name

prodType :: Name_ -> Expr -> Expr
prodType sortName (App [a]) =
  if (getArgName a) == sortName then App [mkArg "Prod", a, a] else App [a] 
prodType _ x = x 

productThry :: Eq.EqTheory -> Eq.EqTheory
productThry t =
 let sortName = getConstrName (t ^. Eq.sort)  
 in set Eq.thyName ("Product") $     
    gmap (prodType sortName) $
    gmap (ren sortName) t

prodTheoryToDecl :: Eq.EqTheory -> Decl
prodTheoryToDecl = Eq.toDecl (++ "C")



 
 
