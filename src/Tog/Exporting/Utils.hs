module Tog.Exporting.Utils where

import Tog.Raw.Abs
import Tog.Instrumentation.Conf (Mode(..)) 

import Control.Lens ((^.))
import Data.List ((\\), isPrefixOf)
import Text.PrettyPrint.Leijen (Doc,text) 
import Data.Generics hiding (Constr, empty)

import Tog.Deriving.Lenses (name)
import Tog.Deriving.TUtils (mkQName, getName, getConstrName)
import Tog.Deriving.StagedTerms (opDeclToFuncName)
import Tog.Deriving.Utils.Renames (foldrenConstrs)
import Tog.Exporting.Config

import qualified Tog.Exporting.Lean.Preprocess as LP
import qualified Tog.Exporting.Agda.Preprocess as AP 

preprocessDecls :: Config -> [Decl] -> [Decl]
preprocessDecls conf decls =
  if target conf == Lean then LP.preprocessDecls decls else AP.preprocessDecls decls

callFunc :: Config -> Expr -> Expr
callFunc conf e =
  if target conf == Lean then LP.callFunc e else AP.callFunc e

replace :: Config -> String -> String
replace conf nm =
  if target conf == Lean then LP.replace nm else AP.replace nm 



universeLevel :: Config -> Fields -> Doc
universeLevel conf flds =
  text $
   if elem "Set" $ everything (++) (mkQ [] (\(Name (_,x)) → [x])) flds
   then (level1 conf) else (level0 conf)

openTheory :: Config -> Module -> Module
openTheory conf m@(Module nm params (Decl_ decls)) =
  if (open_theory conf) then Module nm params (Decl_ (firstPart ++ [Open $ NotQual nm] ++ rest)) else m 
  where firstPart = takeWhile (not . hasModuleName) decls ++ filter hasModuleName decls
        rest = decls \\ firstPart
        hasModuleName (Record rnm _ _) = rnm == nm
        hasModuleName _ = False
openTheory _ m = m

mkImports :: Config -> [String] -> [Decl]
mkImports conf imprts =
  let getNames prefix =
        if prefix == "" then [] else removePrefix conf $ filter (isPrefixOf prefix) imprts
      createImport x = ImportNoArgs $ mkQName x
  in map (\x -> Import $ createImport x) ((getNames $ import_ conf) \\ (getNames $ openimport conf))
     ++ map (\x -> OpenImport $ createImport x) (getNames $ openimport conf)
     ++ map (\x -> Open $ mkQName x) ((getNames $ open_ conf) \\ (getNames $ openimport conf))

removePrefix :: Config -> [String] -> [String] 
removePrefix conf lst =
  let cond x = x /= (open_ conf) && x /= (import_ conf) && x /= (openimport conf)
  in concat $ map (filter cond . words) lst 


splitDecls :: [Decl] -> ([Decl], [Decl])
splitDecls ds = ([d | d <- ds, not (isModule d)],
                 [m | m <- ds, isModule m])
    where isModule (Module_ _) = True
          isModule _ = False 

constructorsAsFunctions :: Config -> [Decl] -> [Decl] 
constructorsAsFunctions conf decls =
  constructorsAsFunctionsHelper conf (foldr (++) [] $ map getDataConstructors decls) decls 
  where getDataConstructors (Data _ _ (DataDef cs)) = cs 
        getDataConstructors (Data _ _ (DataDeclDef _ cs)) = cs
        getDataConstructors _ = [] 

constructorsAsFunctionsHelper :: Config -> [Constr] -> [Decl] -> [Decl] 
constructorsAsFunctionsHelper conf cs decls =
  let cnames = map getConstrName cs
      toFindNames = map opDeclToFuncName cnames 
      mapping = zip toFindNames cnames
   in if(constructors_as_functions conf) then decls 
      else foldrenConstrs mapping $ filter (\d -> not $ elem (declName d) toFindNames) decls 

declName :: Decl -> String 
declName d = case d of
        TypeSig (Sig n _) -> n^.name 
        FunDef n _ _ -> n^.name
        Data n _ _ -> n^.name
        Record n _ _ -> n^.name
        Open qn -> getName qn
        OpenImport (ImportNoArgs qn) -> getName qn
        OpenImport (ImportArgs qn _) -> getName qn
        Import  (ImportNoArgs qn) -> getName qn
        Import (ImportArgs qn _)  -> getName qn
        Postulate _ -> ""
        Module_ (Module n _ _ ) -> n^.name 
