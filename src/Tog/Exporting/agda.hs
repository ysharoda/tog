 {-# LANGUAGE UnicodeSyntax #-}

module Tog.Exporting.Agda where

import Tog.Raw.Abs
import Tog.Deriving.Lenses (name)
import Tog.Deriving.Utils.Bindings (getBindingArgs, getBindingExpr)
import Tog.Deriving.TUtils (getArgExpr, getArgName, getName) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen as PP 
import Data.Generics hiding (Constr, empty)
import Data.List (concat, takeWhile, (\\))
import Data.List.Split (splitOn)
import Data.Char (toUpper) 

-- from out experience, it is useful to have a boolean variable needed in different places for different purposes. In some places it may not be needed, so it can be ignored 
class PrintAgda a where
  printAgda ::  a -> Doc 

instance PrintAgda Name where
  printAgda nm =
    text $ replace (nm ^. name)

instance PrintAgda QName where
  printAgda (Qual qn n) = printAgda qn <> dot <> printAgda n
  printAgda (NotQual n) = printAgda n

instance PrintAgda Constr where 
  printAgda (Constr nm typ)  =
    printAgda nm <+> text ofType <+> printAgda typ

instance PrintAgda Arg where
  printAgda arg = printAgda (getArgExpr arg)

instance PrintAgda Binding where
  printAgda binds =
    let arguments as = foldr (<+>) empty $ map (printAgda) as
        binding x =  arguments (getBindingArgs x) <+> text ofType <+> printAgda (getBindingExpr x) 
    in case binds of
      Bind  _ _ -> parens $ binding binds
      HBind _ _ -> braces $ binding binds

hasPi :: [Expr] -> Bool 
hasPi [] = False 
hasPi ((Pi _ _):_) = True
hasPi (_:xs) = hasPi xs 

instance PrintAgda [Binding] where
  printAgda bindsList =
   foldr (<+>) empty $ map (printAgda) bindsList 
   -- encloseSep empty empty (text pi_representation) $ map printAgdaindsList

instance PrintAgda [Constr] where
  printAgda constrsList = vsep $ map (printAgda) constrsList   

instance PrintAgda Telescope where
  printAgda (Tel binds) = printAgda binds 

instance PrintAgda Expr where
  printAgda (Lam names expr) =
    parens $
     text lambda <+>
     foldr (<+>) empty (map (printAgda) names) <+> 
     text lambdaArrow <+>
     printAgda expr
  printAgda (Pi tel expr) =
    parens $ printAgda tel <+> (if emptyTel tel then empty else text pi_representation) <+> printAgda expr
  printAgda (Fun e1 e2) =
    parens $ printAgda e1 <+> text fun_sep <+> printAgda e2
  printAgda (Eq e1 e2) = -- might need to have a bracket here 
    printAgda e1 <+> text equality_symbol <+> printAgda e2
  printAgda (App args) =
    let (App newargs) = callFunc (App args) 
        pr = foldr (<+>) empty $ map (printAgda) newargs
    in if length args == 1 then pr else parens pr     
  printAgda (Id qname) = printAgda qname

instance PrintAgda Fields where
  printAgda NoFields = empty
  printAgda (Fields cs) = printAgda cs 

instance PrintAgda Params where
  printAgda (ParamDecl binds) = printAgda binds
  printAgda _ = empty 

-- instead of sending the typ to recordHeader, we send the fields to check for the universe. 
instance PrintAgda RecordBody where
  printAgda (RecordDecl _) = recordHeader Nothing  
  printAgda (RecordDef _ flds) = recordHeader (Just flds) PP.<$> recordFields flds 
  printAgda (RecordDeclDef _ constructor flds) =
    recordHeader (Just flds) PP.<$> recordConstructor constructor PP.<$> recordFields flds

instance PrintAgda DataBody where
  printAgda (DataDecl nm) = dataHeader nm 
  printAgda (DataDef cs) = printAgda cs
  printAgda (DataDeclDef nm cs) =
    dataHeader nm PP.<$> (indent 2 $ printAgda cs) 

instance PrintAgda TypeSig where
  printAgda (Sig nm e) =
    printAgda nm <+> text ofType <+> printAgda e

instance PrintAgda Where where
  printAgda NoWhere = empty
  printAgda (Where decls) = text "where" <+> (vsep $ map printAgda decls) 

instance PrintAgda FunDefBody where
  printAgda FunDefNoBody = empty
  printAgda (FunDefBody e wher) = printAgda e PP.<$> printAgda wher

instance PrintAgda Pattern where
  printAgda (EmptyP _) = empty
  printAgda (ConP qnm ptrns) = parens $ printAgda qnm <+> (foldr (<+>) empty $ map (printAgda) ptrns)
  printAgda (IdP qnm) = printAgda qnm
  printAgda (HideP ptrn) = braces $ printAgda ptrn 

instance PrintAgda Import where
  printAgda (ImportNoArgs qn) = printAgda qn
  printAgda (ImportArgs qn args) = printAgda qn <+> (foldr (<+>) empty $ map (printAgda) args) 

instance PrintAgda Decl where
  printAgda (TypeSig typ) = printAgda typ
  printAgda (FunDef nm patterns body) =
    printAgda nm <+> (foldr (<+>) empty $ map (printAgda) patterns) <+> text fundef <+> printAgda body
  printAgda (Data nm params body) =
    (text type_keyword) <+> printAgda nm <+> printAgda params <+> printAgda body <+> linebreak 
  printAgda (Record nm params body) =
    (text record_keyword) <+> printAgda nm <+> printAgda params <+> printAgda body <+> linebreak  
  printAgda (Open imp) = text open <+> printAgda imp
  printAgda (Import imp) = text import_ <+> printAgda imp
  printAgda (OpenImport imp) = text open_import <+> printAgda imp
  printAgda (Module_ m) = linebreak <+> printAgda (addOpenDecl m)  <+> linebreak -- to open the first declaration, which represents the equational theory. 
  printAgda _ = empty

universeLevel :: Fields -> Doc
universeLevel flds =
  text $
  if elem "Set" $ everything (++) (mkQ [] (\(Name (_,x)) → [x])) flds
  then "Set₁" else "Set" 

instance PrintAgda DeclOrLE where
  printAgda (Decl_ decls) = vsep $ map printAgda decls
  printAgda (Lang_ _) = error "theory expressions not accepted by Agda" 

instance PrintAgda Module where
  printAgda (Module nm params decls) =
    text module_ <+> printAgda nm <+>
    printAgda params <+> text module_beforeDecls PP.<$>
    (indent 2 $ printAgda decls)

-- Utils functions --
addOpenDecl :: Module -> Module 
addOpenDecl (Module nm params (Decl_ decls)) =
  Module nm params (Decl_ (firstPart ++ [Open $ NotQual nm] ++ rest)) 
  where firstPart = takeWhile (not . hasModuleName) decls ++ filter hasModuleName decls
        rest = decls \\ firstPart 
        hasModuleName (Record rnm _ _) = rnm == nm
        hasModuleName _ = False 
addOpenDecl m = m
    
emptyTel :: Telescope -> Bool
emptyTel (Tel b) = null b 

-- nm is the type "Set" 
recordHeader :: Maybe Fields -> Doc
recordHeader flds = text ofType <+> universe <+> text record_beforeDecls
  where universe = case flds of
          Nothing -> text "Set"
          Just fs -> universeLevel fs 

-- nm is the constructor name 
recordConstructor :: Name -> Doc
recordConstructor nm = indent 2 $ text record_constructor <+> printAgda nm

recordFields :: Fields -> Doc
recordFields NoFields = empty
recordFields (Fields []) = empty 
recordFields flds =
  indent 2 $ text record_beforeFlds <$$> (indent 2 $ printAgda flds)

dataHeader ∷ Name -> Doc
dataHeader nm = text ofType <+> printAgda nm <+> text type_beforeDecls

-- the config that needs to be imported --
ofType, lambda, lambdaArrow, pi_representation, fun_sep, equality_symbol, record_keyword, record_beforeDecls, record_constructor, record_beforeFlds, equality_import, type_keyword,type_beforeDecls,fundef, open, open_import, import_, module_, module_beforeDecls :: String 
ofType = ":"
lambda = "λ"
lambdaArrow = "→"
pi_representation = "→"
fun_sep = "→"
equality_import = "import Relation.Binary.PropositionalEquality" 
equality_symbol = "≡"
record_keyword = "record"
record_beforeDecls = "where" 
record_constructor = "constructor"
record_beforeFlds = "field"
type_keyword = "data"
type_beforeDecls = "where" 
fundef = "="
open = "open"
open_import = "open import"
import_ = "import"
module_ = "module"
module_beforeDecls = "where"   

{- handling imports -}
--An import replaces one or more of the prelude functions and might have an effect on how the function is called, we handle this here 
-- the input to the exporter is a list of decls that start with some prelude functions. Some systems might have imports to replace these functions. This would be specified as follows

{- 
data PreludeAction =
    DoNotExport
  | ExportAsIs 
  | Replace Doc
-} 
includeJ, includeSubst, includeSym, includeCong, includeTrans, includeUnit, includeEmptyT, includeNat, includePred, includeIsZero, includeZeroNotSuc, includeLemma, includeSucInj, includeFin, includeVec, includeLookup:: Bool
includeJ = False
includeSubst = False
includeSym = False
includeCong = False
includeTrans = False
includeUnit = False
includeEmptyT = False
includeNat = False
includePred = False
includeIsZero = False
includeZeroNotSuc = False
includeLemma = False
includeSucInj = False
includeFin = False
includeVec = False
includeLookup = False

imports :: [Doc]
imports =
  map text ["open import Agda.Builtin.Equality",
            "open import Agda.Builtin.Nat",
            "open import Data.Fin", 
            "open import Data.Vec"]

importNames :: [String]
importNames =
  ["Agda.Builtin.Equality",
   "Agda.Builtin.Nat",
   "Data.Fin", 
   "Data.Vec"]
{-
replaceUnit, replacEmpty, replaceNat, replaceFin, replaceVec :: Maybe Doc 
replaceUnit = Nothing
replacEmpty = Nothing
replaceNat = Nothing
replaceFin = Nothing
replaceVec = Nothing
replaceLookup = Nothing -} 
-- from all the prelude, we only call lookup, Staged and Code.

callFunc :: Expr -> Expr
callFunc a@(App [nm,_,a2,a3]) =
  if (getArgName nm == "lookup") then App [nm,a3,a2] else a
callFunc e = e

replace :: String -> String
replace nm =
  let pieces = splitOn "_" nm
      cond = \x → if (x == "0" || x == "1") then x ++ "ᵢ" else x
      postProcess lst = (head lst) : (map ("_"++) $ tail lst)
  in concat $ postProcess $ map cond pieces 

removeDecl :: String -> [Decl] -> [Decl]
removeDecl _ [] = [] 
removeDecl declNm (d:ds) =
  let headNm = 
        case d of
          TypeSig (Sig nm _) -> nm ^. name
          FunDef nm _ _ -> nm ^. name
          Data nm _ _ -> nm ^. name
          Record nm _ _ -> nm ^. name
          Open qnm -> getName qnm 
          OpenImport (ImportNoArgs qnm) -> getName qnm
          OpenImport (ImportArgs qnm _) -> getName qnm
          Import (ImportNoArgs qnm) -> getName qnm
          Import (ImportArgs qnm _) -> getName qnm
          _ -> "" 
  in if (headNm == declNm) then removeDecl declNm ds else d : removeDecl declNm ds

filterOneDecl :: Bool -> String -> [Decl] -> [Decl]
filterOneDecl flag str ds = if flag then ds else removeDecl str ds
  
filterDecls ::[Decl] -> [Decl]
filterDecls ds = 
  filterOneDecl includeJ "J" $
  filterOneDecl includeSubst "subst" $
  filterOneDecl includeSym "sym" $
  filterOneDecl includeCong "cong" $
  filterOneDecl includeTrans "trans" $
  filterOneDecl includeUnit "Unit" $ 
  filterOneDecl includeEmptyT "EmptyT" $
  filterOneDecl includeNat "Nat" $
  filterOneDecl includePred "pred" $
  filterOneDecl includeIsZero "IsZero" $
  filterOneDecl includeZeroNotSuc "zeroNOTsuc" $
  filterOneDecl includeLemma "lemma" $
  filterOneDecl includeSucInj "sucInj" $
  filterOneDecl includeFin "Fin" $ 
  filterOneDecl includeVec "Vec" $
  filterOneDecl includeLookup "lookup" ds 
 
exportAgda :: String → Module -> Doc
exportAgda moduleName (Module _ params (Decl_ decls)) =
 let dropLast [] = [] 
     dropLast [_] = []
     dropLast (x:xs) = x : dropLast xs 
     tempName = last $ splitOn "/" $ concat $ dropLast $ splitOn "." moduleName 
     nm = (toUpper $ head tempName) : tail tempName
 in 
   text module_ <+>
   printAgda (Name ((0,0),nm)) <+>
   printAgda params <+>
   text module_beforeDecls PP.<$>
   (indent 2 $
     (vsep $ imports ++ map printAgda (filterDecls decls)))
exportAgda _ _ = error "toplevel needs to be a module" 
