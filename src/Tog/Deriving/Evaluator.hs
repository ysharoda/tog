module Tog.Deriving.Evaluator where

import Control.Lens ((^.))

import Tog.Raw.Abs hiding (Open)
import Tog.Deriving.EqTheory as Eq
import Tog.Deriving.Terms
import Tog.Deriving.Utils.Functions
import Tog.Deriving.Utils.Bindings (unionBindings)

import Tog.Deriving.Types (Name_)
import Tog.Deriving.TUtils

evalFuncName :: Term -> String
evalFuncName Basic         = "evalB"
evalFuncName (Closed _)    = "evalCl"
evalFuncName (BasicOpen _)      = "evalOpB"
evalFuncName (Open _ _) = "evalOp" 

envName :: String 
envName = "vars"

{-
eval : {A : Set} -> Monoid A -> MonTerm -> A
eval M ee = (e M)
eval M (opp x y) = (op M) (eval M x) (eval M y)

evalOpenTerm : {A : Set} -> (n : Nat) -> Monoid A -> OpenMonTerm n -> Vec A n -> A
evalOpenTerm n mon (v fin) vars = lookup n fin vars
evalOpenTerm _ mon (e') _ = (e mon) 
evalOpenTerm n mon (op' x y) vars = (op mon) (evalOpenTerm n mon x vars) (evalOpenTerm n mon y vars)

evalClTerm : {A : Set} -> Monoid A -> ClMonTerm A -> A
evalClTerm _ mon (eCl) = (e mon)
evalClTerm _ mon (sing x) = x 

evalOpE : {A : Set} -> (n : Nat) -> Monoid A -> OpExtMonTerm n -> Vec A n -> A
evalOpE _ n mon (v fin) vars = lookup 

1. the bindings for the term language + the bindings for the eq theory --> take their union
2. instance of monoid
3. instance of the term language
4. instance of Vec A n
5. Carrier
-- ---------
mkPattern constr --- functor 
-}

-- the type signature for the evaluation function 
typeSig :: EqTheory -> TermLang -> TypeSig
typeSig thry termlang =
 let
   (_,eqbind,eqinst) = eqInstance thry Nothing
   (tbind,tinst) = tlangInstance termlang
   newBinds = unionBindings eqbind tbind
   sortExpr = projectConstr thry ""  (thry ^. sort)
   trmTy = getTermType termlang
 in Sig (mkName $ evalFuncName trmTy) $
   if null newBinds then Fun eqinst (Fun tinst sortExpr)
   else Pi (Tel newBinds) $
         Fun eqinst $
            case trmTy of
              Basic -> Fun tinst sortExpr
              Closed _ -> Fun tinst sortExpr 
              BasicOpen n -> Fun (vecApp (getConstrName $ thry ^. sort) n) $ Fun tinst sortExpr 
              Open n c -> Fun (vecApp c n) $ Fun tinst sortExpr  

vecApp :: Name_ -> Name_ -> Expr
vecApp carrierName natName = App [mkArg "Vec", mkArg carrierName, mkArg natName] 

-- Problem: If the carrier is not a param to the theory, the type might be
-- Monoid -> MonTerm -> XXX how do we refer to the carrier of the monoid here? 


-- pattern matching on the constructors 
adjustPattern :: Name_ -> Term -> Pattern -> [Pattern]
adjustPattern tinstName term pat =
 let base = [IdP $ mkQName tinstName, pat]
     extBase i = [IdP $ mkQName i, IdP $ mkQName tinstName, IdP $ mkQName envName, pat]
 in case term of
    Basic -> base 
    (Closed _) -> base
    (BasicOpen n) -> extBase n
    (Open n _ ) -> extBase n
                
funcDef :: EqTheory -> Name_ -> Term -> Constr -> Expr  
funcDef thry instName term constr = 
 let cexpr = applyProjConstr thry instName constr
     basicArgs = App [mkArg $ evalFuncName term, mkArg instName]
     extArgs i = App [mkArg $ evalFuncName term, mkArg i, mkArg instName, mkArg envName]
  in case term of
       Basic -> functor' basicArgs cexpr 
       Closed _ -> functor' basicArgs cexpr 
       BasicOpen n -> functor' (extArgs n) cexpr 
       Open n _ -> functor' (extArgs n) cexpr 

patternsExprs :: EqTheory -> TermLang -> Name_ -> [(Pattern,Expr)]
patternsExprs thry (TermLang term _ _ constrs) thryInstName =
{-  if not (null vs) then [(mkPattern $ head vs, lookup' "n" envName)] else []
  ++ if not (null cs) then [(mkPattern $ head cs, constFunc)] else []
  ++ zipWith ((,)) (map mkPattern typDecls) (map (funcDef thry thryInstName term) thryDecls)-}
  zipWith ((,)) (map mkPattern (vs ++ cs ++ typDecls)) $ 
                [lookup' "n" envName | not (null vs)] 
                ++ [constFunc | not (null cs)] 
                ++ map (funcDef thry thryInstName term) thryDecls 
  where vs = filter isVarDecl  constrs
        cs = filter isConstDecl constrs
        thryDecls = (thry ^. funcTypes)
        typDecls  = filter (not . isConstOrVar) constrs

lookup' :: Name_ -> Name_ -> Expr
lookup' natVarName vName =
  App [mkArg "lookup", mkArg natVarName, mkArg "x1", mkArg vName]

constFunc :: Expr
constFunc = App [mkArg "x1"]

oneEvalFunc :: EqTheory -> TermLang -> [Decl]
oneEvalFunc _ (TermLang _ _ _ []) = []
oneEvalFunc eq tl =
  (TypeSig $ typeSig eq tl) :
  map (\(p,e) -> FunDef (mkName $ evalFuncName term) (adjustPattern thryInstName term p) (mkFunDefBody e))
      (patternsExprs eq tl thryInstName)
  where thryInstName = twoCharName (eq ^. thyName) 0
        term = getTermType tl

{-
  zipWith (FunDef (mkName $ evalFuncNames) 

  let    
 
  in 
  [TypeSig $ typeSig eq termLang] ++ -- type 
     [FunDef (mkName $ evalFuncName term) -- call for vars
         (concatMap (cpattern instName term) vs)
         (lookup' "n" envName) | not (null vs)] ++ 
     [FunDef (mkName $ evalFuncName term) -- call for constants 
         (concatMap (cpattern instName term) constants)
         constFunc | not (null constants)] ++ 
     zipWith (FunDef (mkName $ evalFuncName term)) -- call for every func symbol 
             (map (cpattern instName term) tDecls)
             (map (funcDef eq instName term) eqDecls)
-}
evalFuncs :: EqTheory -> [TermLang] -> [Decl]
evalFuncs eq = concatMap (oneEvalFunc eq)

--evalOpenTerm : {A : Set} -> (n : Nat) -> Monoid A -> OpenMonTerm n -> Vec A n -> A
--evalOpenTerm n mon (v fin) vars = lookup n fin vars
--evalOpenTerm n mon (op' x y) vars = (op mon) (evalOpenTerm n mon x vars) (evalOpenTerm n mon y vars)
