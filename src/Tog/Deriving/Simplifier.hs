module Tog.Deriving.Simplifier where

import Tog.Raw.Abs hiding (Open) 
import Tog.Deriving.Utils.Functions 
import Tog.Deriving.TUtils (mkName, mkArg, getConstrName)
import Tog.Deriving.EqTheory 
import Tog.Deriving.Terms
import Tog.Deriving.Utils.Renames (foldrenConstrs)
import Tog.Deriving.Utils.Bindings (getBindingArgs)

import Control.Lens ((^.))
import Data.Generics (everything, mkQ)
import Data.Map as Map (toList) 

type Rule = Constr

-- Utils
simpFuncNm :: Term -> String
simpFuncNm Basic       = "simplifyB"
simpFuncNm (Closed _)    = "simplifyCl"
simpFuncNm (BasicOpen _)      = "simplifyOpB"
simpFuncNm (Open _ _) = "simplifyOp" 

explength :: Expr -> Int
explength e = everything (+) (mkQ 0 $ \(Name _) -> 1) e

constrlength :: Constr -> Int
constrlength (Constr _ e) = 1 + explength e

minMax :: Expr -> Expr -> Maybe (Expr,Expr)
minMax e1 e2 =
  if (explength e1 == explength e2) then Nothing
  else if explength e1 < explength e2 then Just (e1,e2)
  else Just (e2,e1) 

gatherVars :: Telescope -> [String]
gatherVars (Tel binds) =
  everything (++) (mkQ [] (\(Name (_,nm)) -> [nm])) $ map getBindingArgs binds

count :: Expr -> String -> Int 
count e el = everything (+) (mkQ 0 (\(Name (_,nm)) -> if nm == el then 1 else 0)) e 
  
isLinear :: Expr -> Bool
isLinear (Pi tel e) =
  let vs = gatherVars tel
      occurences = map (count e) vs
  in null $ filter (/= 1) occurences
isLinear _ = True 

-- The type signature of the simplifier functions
{-
simplifyB :: MonTerm -> MonTerm
simplifyCl :: {A : Term} -> MonTerm A -> MonTerm A
simplifyOp :: {n : Nat} -> MonTerm n -> MonTerm n
simplifyOpExt :: {A : Term} {n : Nat} -> MonTerm n A -> MonTerm n A 
-} 
typesig :: Term -> TermLang -> TypeSig
typesig term tl =
 Sig (mkName (simpFuncNm term)) $ typeExpr term 
 where
  (binds,typApp) = tlangInstance tl
  typeExpr Basic = Fun typApp typApp
  typeExpr _     = Pi (Tel binds) (Fun typApp typApp)


-- Given a Constr that is an equality , if one of the sides have length less than the other, then we create a pattern match 
simplify :: Constr -> Maybe (Pattern,FunDefBody) 
simplify (Constr _ e) = 
 case e of
   Eq e1 e2 -> helper e1 e2 
   Pi p (Eq e1 e2) ->
      if (isLinear (Pi p e1)) && (isLinear (Pi p e2))
      then helper e1 e2
      else Nothing 
   _ -> Nothing
 where
   helper e1 e2 =
     case minMax e1 e2 of
       Nothing -> Nothing
       Just (mn,mx) ->
         Just (mkPattern mx,mkFunDefBody mn)

-- ---------------------------------------------------------------- 

adjustFuncCalls :: Term -> Expr
adjustFuncCalls Basic = App [mkArg $ simpFuncNm Basic]
adjustFuncCalls (Closed x) = App $ (mkArg $ simpFuncNm (Closed x)):(mkArg "_"):[]
adjustFuncCalls (BasicOpen x)   = App $ (mkArg $ simpFuncNm (BasicOpen x)):(mkArg "_"):[]
adjustFuncCalls (Open x y) = App $ (mkArg $ simpFuncNm (Open x y)):(mkArg "_"):(mkArg "_"):[]

adjustPattern :: Term -> Pattern -> [Pattern]
adjustPattern term x = (underscorePattern term) ++ [x]

-- simplification rules 
simpRules :: Term -> [Constr] -> [Decl]
simpRules term axms=
 let
  rules = filter (/= Nothing) $ map simplify axms
 in map (\(Just (x,y)) -> FunDef (mkName $ simpFuncNm term) (adjustPattern term x) y) rules

-- the recursive cases 
simpDecls :: Term -> [Constr] -> [Decl]
simpDecls term ftyps =
  let patterns = map mkPattern ftyps
      fundefs = map (functor' (adjustFuncCalls term) . fappExpr) ftyps
  in
    zipWith (mkFunDef $ simpFuncNm term) (map (adjustPattern term) patterns) fundefs  

simpVarsConsts :: Term -> [Constr] -> [Decl]
simpVarsConsts term cs =
  zipWith (mkFunDef (simpFuncNm term)) (map (adjustPattern term . mkPattern) cs) (map fappExpr cs)
  


oneSimpFunc :: EqTheory -> TermLang -> [Decl]
oneSimpFunc _ (TermLang _ _ _ []) = []
oneSimpFunc thry termLang@(TermLang term _ _ constrs) =
 let axms = map (foldrenConstrs (Map.toList $ mapping thry term)) (thry ^. axioms) 
     check c = elem (getConstrName c) [v1,v2,sing,sing2]
     varsConsts = filter check  constrs
     fdecls = filter (not . check) constrs
 in 
  TypeSig (typesig term termLang) : 
  (simpRules term axms ++
   simpDecls term fdecls ++
   simpVarsConsts term varsConsts)

-- Given one of the term languages, generate the simplification function 
simplifyFuncs :: EqTheory -> [TermLang] -> [Decl] 
simplifyFuncs thry tlangs =
  concatMap (oneSimpFunc thry) tlangs
  
