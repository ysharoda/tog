module Tog.Deriving.Simplifier where

import Tog.Raw.Abs hiding (Open) 
import Tog.Deriving.Utils.Functions 
import Tog.Deriving.TUtils (mkName, mkArg, getConstrName)
import Tog.Deriving.EqTheory 
import Tog.Deriving.Utils.Types
import Tog.Deriving.Terms
import Tog.Deriving.Utils.Renames (foldrenConstrs)

import Control.Lens ((^.))
import Data.Generics (everything, mkQ)
import Data.Map as Map (toList) 

type Rule = Constr

-- Utils
simpFuncNm :: Term -> String
simpFuncNm Basic       = "simplifyB"
simpFuncNm (Closed _)    = "simplifyCl"
simpFuncNm (Open _)      = "simplifyOp"
simpFuncNm (ExtOpen _ _) = "simplifyOpE" 

explength :: Expr -> Int
explength e = everything (+) (mkQ 0 $ \(Name _) -> 1) e

constrlength :: Constr -> Int
constrlength (Constr _ e) = 1 + explength e

minMax :: Expr -> Expr -> Maybe (Expr,Expr)
minMax e1 e2 =
  if (explength e1 == explength e2) then Nothing
  else if explength e1 < explength e2 then Just (e1,e2)
  else Just (e2,e1) 

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

-- ---------------------------------------------------------------- 

adjustFuncCalls :: Term -> Expr
adjustFuncCalls Basic = App [mkArg $ simpFuncNm Basic]
adjustFuncCalls (Closed x) = App $ (mkArg $ simpFuncNm (Closed x)):(mkArg "_"):[]
adjustFuncCalls (Open x)   = App $ (mkArg $ simpFuncNm (Open x)):(mkArg "_"):[]
adjustFuncCalls (ExtOpen x y) = App $ (mkArg $ simpFuncNm (ExtOpen x y)):(mkArg "_"):(mkArg "_"):[]


-- simplification rules 
simpRules :: Term -> [Constr] -> [Decl]
simpRules term axms=
 let
  rules = filter (/= Nothing) $ map simplify axms
 in map (\(Just (x,y)) -> FunDef (mkName $ simpFuncNm term) (underscorePattern term ++ [x]) y) rules 

-- the recursive cases 
simpDecls :: Term -> [Constr] -> [Decl]
simpDecls term ftyps =
  let patterns = map mkPattern ftyps
      fundefs = map (functor' (adjustFuncCalls term) . fappExpr) ftyps
  in
    zipWith (\x y -> FunDef (mkName $ simpFuncNm term) (underscorePattern term ++ [x]) (FunDefBody y NoWhere)) patterns fundefs     

simpVarsConsts :: Term -> [Constr] -> [Decl]
simpVarsConsts term cs =
  map (\c -> FunDef (mkName $ simpFuncNm term) (underscorePattern term ++ [mkPattern c]) (FunDefBody (fappExpr c) NoWhere)) cs  
  
simpFuncType :: Term -> Decl -> Decl
simpFuncType term datatype =
 TypeSig $ Sig (mkName (simpFuncNm term)) $ typeExpr term datatype
 where
  typeExpr Basic dt =
   let DTApp _ typApp = tapp dt Nothing
   in Fun typApp typApp
  typeExpr _ dt =
   let DTApp binds typApp = tapp dt Nothing
   in  Pi (Tel binds) (Fun typApp typApp)
{-
simplifyB :: MonTerm -> MonTerm
simplifyCl :: {A : Term} -> MonTerm A -> MonTerm A
simplifyOp :: {n : Nat} -> MonTerm n -> MonTerm n
simplifyOpExt :: {A : Term} {n : Nat} -> MonTerm n A -> MonTerm n A 
-} 

oneSimpFunc :: EqTheory -> TermLang -> [Decl]
oneSimpFunc thry termLang@(TermLang term _ _ constrs) =
 let axms = map (foldrenConstrs (Map.toList $ mapping thry term)) (thry ^. axioms) 
     check c = (getConstrName c == v1 || getConstrName c == v2 || getConstrName c == sing || getConstrName c == sing2)
     varsConsts = filter check  constrs
     fdecls = filter (not . check) constrs
 in 
  (simpFuncType term $ tlToDecl termLang) : 
  (simpRules term axms ++
   simpDecls term fdecls ++
   simpVarsConsts term varsConsts)

-- Given one of the term languages, generate the simplification function 
simplifyFuncs :: EqTheory -> [TermLang] -> [Decl] 
simplifyFuncs thry tlangs =
  concatMap (oneSimpFunc thry) tlangs
  
-- simplifyB :: MonTerm -> MonTerm
-- simplifyB (op e x) = x
-- simplifyB (op x e) = x
-- simplifyB (op x y) = op (simplifyB x) (simplifyB y) 
-- simplifyB x = x 

-- simplifyCl (opC e x) = x
-- simplifyCl (opC x e) = x
