module Tog.Deriving.Simplifier where

import Tog.Raw.Abs
import Tog.Deriving.Utils.Functions 
import Tog.Deriving.EqTheory
import Tog.Deriving.TUtils (mkName, mkArg)
import qualified Tog.Deriving.TermLang as TL (termLangNm,mapping)
import Tog.Deriving.Utils.Renames (foldren)

import Data.Generics (everything, mkQ)
import Control.Lens ((^.))
import Data.Map as Map (toList) 

type Rule = Constr

-- Utils

simpFunNm :: String
simpFunNm = "simplify" 

explength :: Expr -> Int
explength e = everything (+) (mkQ 0 $ \(Name _) -> 1) e

constrlength :: Constr -> Int
constrlength (Constr _ e) = 1 + explength e

minMax :: Expr -> Expr -> Maybe (Expr,Expr)
minMax e1 e2 =
  if (explength e1 == explength e2) then Nothing
  else if explength e1 < explength e2 then Just (e1,e2)
  else Just (e2,e1) 

mkFunDef :: Expr -> FunDefBody
mkFunDef e = FunDefBody e NoWhere 

-- Given a Constr that is an equality , if one of the sides have length less than the other, then we create a pattern match 
simplify :: Constr -> Maybe (Pattern,FunDefBody) 
simplify (Constr _ e) = 
 case e of
   Eq e1 e2 -> helper e1 e2 
   Pi _ (Eq e1 e2) -> helper e1 e2 
   _ -> Nothing
 where
   helper e1 e2 =
     case minMax e1 e2 of
       Nothing -> Nothing
       Just (mn,mx) ->
         Just (mkPattern mx,mkFunDef mn)

-- The type of the simplify function 
simpType :: EqTheory -> Decl
simpType eq =
  TypeSig $ mkSimpTypeSig simpFunNm (take 2 $ repeat$  mkArg (TL.termLangNm eq)) 

-- simplification rules 
simpRules :: [Constr] -> [Decl]
simpRules axms=
 let
  rules = filter (/= Nothing) $ map simplify axms
 in map (\(Just (x,y)) -> FunDef (mkName simpFunNm) [x] y) rules 

-- the recursive cases 
simpDecls :: [Constr] -> [Decl]
simpDecls ftyps =
  let patterns = map mkPattern ftyps
      fundefs = map (functor "simplify" . fapp) ftyps
  in
    zipWith (\x y -> FunDef (mkName simpFunNm) [x] (FunDefBody y NoWhere)) patterns fundefs      


simplifyFunc :: EqTheory -> [Decl]
simplifyFunc eq =
 let
  neweq = foldren eq (Map.toList $ TL.mapping eq)
  axms = neweq ^. axioms 
  fTyps = neweq ^. funcTypes 
 in simpType eq : (simpRules axms) ++ (simpDecls fTyps)

