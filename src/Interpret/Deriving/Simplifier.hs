module Interpret.Deriving.Simplifier where

import Tog.Raw.Abs hiding (Open) 
import Interpret.Utils.Functions 
import Interpret.Utils.TUtils (mkName, mkArg)
import Interpret.Deriving.EqTheory 
import Interpret.Deriving.Terms
import Interpret.Utils.Renames (foldrenConstrs)
import Interpret.Utils.Bindings (getBindingArgs, hiddenBind)

import Control.Lens ((^.))
import Data.Generics (everything, mkQ)
import Data.Map as Map (toList)
import Data.Maybe (mapMaybe)

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
typesig :: TermLang -> TypeSig
typesig tl =
 Sig (mkName (simpFuncNm term)) $ typeExpr term 
 where
  (_,binds,typApp) = tlangInstance tl
  typeExpr Basic = Fun typApp typApp
  typeExpr _     = Pi (Tel $ map hiddenBind binds) (Fun typApp typApp)
  term = getTermType tl 


-- ------------------ Adjusting the call functions ---------------- 

-- Given a Constr that is an equality , if one of the sides have length less than the other, then we create a pattern match 
simplify :: Constr -> Maybe (Pattern,Expr) 
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
         Just (mkPattern mx,mn)

adjustFuncCalls :: Term -> Expr
adjustFuncCalls Basic = App [mkArg $ simpFuncNm Basic]
adjustFuncCalls (Closed x) = App $ [mkArg $ simpFuncNm (Closed x)]
adjustFuncCalls (BasicOpen x)   = App $ [mkArg $ simpFuncNm (BasicOpen x)]
adjustFuncCalls (Open x y) = App $ [mkArg $ simpFuncNm (Open x y)]

adjustPattern :: Pattern -> [Pattern]
adjustPattern x = [x] 

-- simplification rules
-- the type of the term language is used to select the mapping to apply 
simpRules :: EqTheory -> Term -> [(Pattern,Expr)]
simpRules thry term =
 let
  mpng = Map.toList $ mapping thry term
  axms = map (foldrenConstrs mpng) (thry ^. axioms) 
 in mapMaybe simplify axms

-- the recursive cases 
simpDecls :: Term -> [Constr] -> [(Pattern,Expr)]
simpDecls term ftyps =
   zipWith ((,)) patterns fundefs
   where patterns = map mkPattern ftyps
         fundefs = map (functor' (adjustFuncCalls term) . fappExpr) ftyps

simpVarsConsts :: [Constr] -> [(Pattern,Expr)]
simpVarsConsts cs =
  zipWith ((,)) (map mkPattern cs) (map fappExpr cs)

-- --------------- Putting it all together ------------------- 
patternsExprs :: EqTheory -> TermLang -> [(Pattern,Expr)]
patternsExprs thry (TermLang term _ _ cs) =
  simpRules thry term
  ++ simpDecls term (filter (not . isConstOrVar) cs)
  ++ simpVarsConsts (filter isConstOrVar cs) 
  
oneSimpFunc :: EqTheory -> TermLang -> [Decl]
oneSimpFunc _ (TermLang _ _ _ []) = []
oneSimpFunc thry tl =
  TypeSig (typesig tl) :  
  map (\(p,e) -> FunDef (mkName $ simpFuncNm term) (adjustPattern p) (mkFunDefBody e))
      (patternsExprs thry tl)
  where term = getTermType tl 

simplifyFuncs :: EqTheory -> [TermLang] -> [Decl] 
simplifyFuncs thry tlangs =
  concatMap (oneSimpFunc thry) (filter (\t -> getTermType t /= Basic) tlangs)
  
