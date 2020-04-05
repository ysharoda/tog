module Tog.Deriving.ProductTheory
  ( prodType
  , prodTheoryToDecl
  , productThry
  ) where

import           Tog.Raw.Abs
import           Tog.Deriving.TUtils
import           Tog.Deriving.Types (gmap, Name_)
import qualified Tog.Deriving.EqTheory as Eq

data ProductTheory = ProductTheory {
  prodName :: Name_    ,
  sort     :: Constr   , 
  funcs    :: [Constr] , 
  axioms   :: [Constr] , 
  waist    :: Int   }

productThry :: Eq.EqTheory -> ProductTheory
productThry thry =
  let -- apply renames to avoid the shadowing problem of Tog
      ren (Name (_,x)) = if (x == "Set") then mkName x else mkName $ x++"P"
      renThry = gmap ren thry 
      thrySort = Eq.sort renThry
  in ProductTheory
   (prodThryName renThry) 
   (thrySort)
   (map (productField $ getConstrName thrySort) (Eq.funcTypes renThry))
   (map (productField $ getConstrName thrySort) (Eq.axioms renThry))
   (Eq.waist renThry)

prodThryName :: Eq.EqTheory -> Name_
prodThryName thry = Eq.thryName thry ++ "Prod"

-- prod type declaration 
-- data Prod (A : Set) (B : Set) : Set
prodType :: Decl 
prodType =
  Data (mkName "Prod")
  (ParamDecl [Bind [mkArg "A", mkArg "B"] $ notQualDecl "Set"])
  (DataDeclDef (mkName "Set") [])  

prodTyp :: Name_ -> Expr
prodTyp sortName =
  let aSort = mkArg sortName in App [mkArg "Prod", aSort, aSort]      

productField :: Name_ -> Constr -> Constr
productField origSort constr =
  let adjustSort arg@(App [Arg (Id (NotQual (Name (_,srt))))]) =
        if (srt == origSort) then prodTyp srt else arg
      adjustSort x = x  
  in gmap adjustSort constr

params :: ProductTheory -> Params
params pt = if (waist pt == 0) then NoParams
  else let pars = take (waist pt) ([sort pt] ++ (funcs pt) ++ (axioms pt))
       in ParamDecl $ map fldsToBinding pars     

prodTheoryToDecl :: ProductTheory -> Decl
prodTheoryToDecl pthry@(ProductTheory nm srt fs axs wst) =
  Record (mkName nm)
    (params pthry)
    (RecordDeclDef (mkName "Set") (mkName $ nm ++ "C") 
      (mkField $ drop wst (srt : fs ++ axs)))
