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

data ProductTheory = ProductTheory {
  prodName :: Name     ,
  sort     :: Constr   , 
  funcs    :: [Constr] , 
  axioms   :: [Constr] , 
  waist    :: Int   }

productThry :: Eq.EqTheory -> ProductTheory
productThry t =
  let -- apply renames to avoid the shadowing problem of Tog
      ren x = if (x^.name == "Set") then x else over name (++"P") x
      t' = gmap ren t
      srt = Eq.sort t'
      mkProd = productField $ getConstrName srt
  in ProductTheory (prodThryName t') srt
   (map mkProd (Eq.funcTypes t'))
   (map mkProd (Eq.axioms t'))
   (Eq.waist t')

prodThryName :: Eq.EqTheory -> Name
prodThryName thry = mkName $ Eq.thryName thry ++ "Prod"

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
        if (srt == origSort) then prodTyp srt else arg
      adjustSort x = x  
  in gmap adjustSort constr

params :: ProductTheory -> Params
params pt = mkParams $ map fldsToBinding $ 
  take (waist pt) (sort pt : (funcs pt) ++ (axioms pt))

prodTheoryToDecl :: ProductTheory -> Decl
prodTheoryToDecl pthry@(ProductTheory nm srt fs axs wst) =
  Record nm (params pthry)
    (RecordDeclDef setType (over name (++ "C") nm)
      (mkField $ drop wst (srt : fs ++ axs)))
