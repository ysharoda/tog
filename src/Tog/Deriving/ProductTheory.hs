module Tog.Deriving.ProductTheory
  ( prodType
  , prodTheoryToDecl
  , productThry
  ) where

import           Control.Lens ((^.), over)

import           Tog.Raw.Abs
import           Tog.Deriving.TUtils
import           Tog.Deriving.Types (gmap, Name_)
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Lenses   (name)

-- There is no need for a new data-structure!
productThry :: Eq.EqTheory -> Eq.EqTheory
productThry t =
  let -- apply renames to avoid the shadowing problem of Tog
      ren x = if x^.name == "Set" then x else over name (++"P") x
      t' = gmap ren t
      srt = t' ^. Eq.sort
      mkProd = productField $ getConstrName srt
  in 
  over Eq.thyName (++ "Prod") $
  over Eq.funcTypes (map mkProd) $
  over Eq.axioms (map mkProd)
  t'

-- prod type declaration 
-- data Prod (A : Set) (B : Set) : Set
prodType :: Decl 
prodType =
  Data (mkName "Prod")
  (ParamDecl [Bind [mkArg "A", mkArg "B"] $ notQualDecl "Set"])
  (DataDeclDef setType [])  

prodTyp :: Name_ -> Expr
prodTyp nm = let n = mkArg nm in App [mkArg "Prod", n, n]

productField :: Name_ -> Constr -> Constr
productField origSort constr =
  let adjustSort arg@(App [Arg (Id (NotQual (Name (_,srt))))]) =
        if srt == origSort then prodTyp srt else arg
      adjustSort x = x  
  in gmap adjustSort constr

prodTheoryToDecl :: Eq.EqTheory -> Decl
prodTheoryToDecl = Eq.toDecl (++ "C")
