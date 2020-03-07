module Tog.ProductTheory where

import Tog.Raw.Abs
import Tog.TUtils
import Tog.EqTheory

import qualified Data.Generics as Generics

data Product = Product Constr Constr

data ProductTheory = ProductTheory {
  prodName :: Name_    ,
  sort     :: Constr   , 
  funcs    :: [Constr] , 
  axioms   :: [Constr] , 
  waist    :: Int   }

productThry :: EqTheory -> ProductTheory
productThry thry =
  let -- apply renames to avoid the shadowing problem of Tog
      ren (Name (_,x)) = if (x == "Set") then mkName x else mkName $ x++"P"
      renThry = Generics.everywhere (Generics.mkT ren) thry 
      thrySort = getSort renThry
  in ProductTheory
   (prodThryName renThry) 
   (thrySort)
   (map (productField $ getConstrName thrySort) (getFuncTypes renThry))
   (map (productField $ getConstrName thrySort) (getAxioms renThry))
   (getWaist renThry)

prodThryName :: EqTheory -> Name_
prodThryName thry = getThryName thry ++ "Prod"

-- Generate the prod type declaration 
-- data Prod (A : Set) (B : Set) : Set
genProdType :: Decl 
genProdType =
  Data (mkName "Prod")
  (ParamDecl [Bind [Arg $ createId "A",Arg $ createId "B"]
     $ App [Arg $ createId "Set"]])
  (DataDeclDef (mkName "Set") [])  

prodSortName :: Name -> Name
prodSortName (Name (_,n)) = mkName $ "Prod" ++ n  

--sortConstr ++ prodSort ++ ba2i with replacement 

prodTyp :: Name_ -> Expr
prodTyp sortName =
  let nameAsArg = Arg $ createId $ sortName
  in App [Arg $ createId "Prod", nameAsArg, nameAsArg]      


productSort :: Constr -> Constr
productSort sortC =
  let nameAsArg = Arg $ createId $ getConstrName sortC
      prodtyp   = App [Arg $ createId "Prod", nameAsArg, nameAsArg]      
  in Constr (prodSortName $ mkName $ getConstrName sortC) prodtyp

productField :: Name_ -> Constr -> Constr
productField origSort constr =
  let adjustSort arg@(App [Arg (Id (NotQual (Name (_,srt))))]) =
        if (srt == origSort) then prodTyp srt else arg
      adjustSort x = x  
  in Generics.everywhere (Generics.mkT $ adjustSort) constr 

params :: ProductTheory -> Params
params pt = if (waist pt == 0) then NoParams
  else let pars = take (waist pt) ([sort pt] ++ (funcs pt) ++ (axioms pt))
       in ParamDecl $ map fldsToBinding pars     

fldsToBinding :: Constr -> Binding
fldsToBinding (Constr nm typ) =
  Bind [Arg $ createId $ getNameAsStr nm] typ 

prodTheoryToDecl :: ProductTheory -> Decl
prodTheoryToDecl pthry@(ProductTheory nm srt fs axs wst) =
  Record (mkName nm)
    (params pthry)
    (RecordDeclDef (mkName "Set") (mkName $ nm ++ "C") 
      (let flds = drop wst ([srt] ++ fs ++ axs)
       in if flds == [] then NoFields else Fields flds))


{-

[Data (Name ((0,0),"Prod")) (ParamDecl [Bind [Arg (Id (NotQual (Name ((0,0),"A")))),Arg (Id (NotQual (Name ((0,0),"B"))))] (App [Arg (Id (NotQual (Name ((0,0),"Set"))))])]) (DataDecl (Name ((0,0),"Set"))),

Module_ (Module (Name ((0,0),"Carrier")) NoParams (Decl_ [Record (Name ((0,0),"Carrier")) NoParams (RecordDeclDef (Name ((0,0),"Set")) (Name ((0,0),"CarrierC")) (Fields [Constr (Name ((4,25),"A")) (App [Arg (Id (NotQual (Name ((4,29),"Set"))))])]))])),Module_ (Module (Name ((0,0),"Empty")) NoParams (Decl_ [Record (Name ((0,0),"Empty")) NoParams (RecordDeclDef (Name ((0,0),"Set")) (Name ((0,0),"EmptyC")) NoFields)])),Module_ (Module (Name ((0,0),"Magma")) NoParams (Decl_ [Record (Name ((0,0),"Magma")) NoParams (RecordDeclDef (Name ((0,0),"Set")) (Name ((0,0),"MagmaC")) (Fields [Constr (Name ((4,25),"A")) (App [Arg (Id (NotQual (Name ((4,29),"Set"))))]),Constr (Name ((6,25),"op")) (Fun (App [Arg (Id (NotQual (Name ((6,30),"A"))))]) (Fun (App [Arg (Id (NotQual (Name ((6,35),"A"))))]) (App [Arg (Id (NotQual (Name ((6,40),"A"))))])))])),Record (Name ((0,0),"MagmaProd")) NoParams (RecordDeclDef (Name ((0,0),"Set")) (Name ((0,0),"MagmaProdC")) (Fields [Constr (Name ((4,25),"A")) (App [Arg (Id (NotQual (Name ((4,29),"Set"))))]),Constr (Name ((0,0),"ProdA")) (App [Arg (Id (NotQual (Name ((0,0),"Prod")))),Arg (Id (NotQual (Name ((0,0),"A")))),Arg (Id (NotQual (Name ((0,0),"A"))))]),
Constr (Name ((6,25),"op")) (Fun (App [Arg (Id (NotQual (Name ((0,0),"ProdA"))))]) (Fun (App [Arg (Id (NotQual (Name ((0,0),"ProdA"))))]) (App [Arg (Id (NotQual (Name ((0,0),"ProdA"))))])))]))])),Module_ (Module (Name ((0,0),"Pointed")) NoParams (Decl_ [Record (Name ((0,0),"Pointed")) NoParams (RecordDeclDef (Name ((0,0),"Set")) (Name ((0,0),"PointedC")) (Fields [Constr (Name ((4,25),"A")) (App [Arg (Id (NotQual (Name ((4,29),"Set"))))]),Constr (Name ((5,27),"e")) (App [Arg (Id (NotQual (Name ((5,31),"A"))))])])),Record (Name ((0,0),"PointedProd")) NoParams (RecordDeclDef (Name ((0,0),"Set")) (Name ((0,0),"PointedProdC")) (Fields [Constr (Name ((4,25),"A")) (App [Arg (Id (NotQual (Name ((4,29),"Set"))))]),Constr (Name ((0,0),"ProdA")) (App [Arg (Id (NotQual (Name ((0,0),"Prod")))),Arg (Id (NotQual (Name ((0,0),"A")))),Arg (Id (NotQual (Name ((0,0),"A"))))]),Constr (Name ((5,27),"e")) (App [Arg (Id (NotQual (Name ((0,0),"ProdA"))))])]))]))])


-} 
