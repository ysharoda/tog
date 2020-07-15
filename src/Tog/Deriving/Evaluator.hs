module Tog.Deriving.Evaluator where

import Control.Lens ((^.))
import Data.List (union)

-- import Tog.Deriving.TypeConversions
-- import Tog.Parse as P
-- import Tog.Deriving.Main
import Tog.Raw.Abs hiding (Open)
import Tog.Deriving.EqTheory as Eq
import Tog.Deriving.Terms --(termLangNm)
import Tog.Deriving.Utils.Types
import Tog.Deriving.Utils.Functions
import Tog.Deriving.Utils.Bindings (unionBindings)

import Tog.Deriving.Types (Name_)
import Tog.Deriving.TUtils

import Data.List ((\\),union)

evalFuncName :: Term -> String
evalFuncName Basic         = "evalB"
evalFuncName (Closed _)    = "evalCl"
evalFuncName (Open _)      = "evalOp"
evalFuncName (ExtOpen _ _) = "evalOpE" 

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

vecApp :: Name_ -> Name_ -> Expr
vecApp carrierName natName = App [mkArg "Vec", mkArg carrierName, mkArg natName] 

-- Problem: If the carrier is not a param to the theory, the type might be
-- Monoid -> MonTerm -> XXX how do we refer to the carrier of the monoid here? 
ftype :: EqTheory -> TermLang -> TypeSig
ftype thry termlang =
 let
   (tbind,tinst) = eqApp thry Nothing
   DTApp lbind linst = tapp (tlToDecl termlang) Nothing
   newBinds = unionBindings tbind lbind
   sortExpr = projectConstr thry ""  (thry ^. sort)
   trmTy = getTermType termlang
 in Sig (mkName $ evalFuncName trmTy) $
   if (newBinds == []) then Fun tinst (Fun linst sortExpr)
   else Pi (Tel newBinds) $
         Fun tinst $
            case trmTy of
              Basic -> Fun linst sortExpr
              Closed _ -> Fun linst sortExpr 
              Open n -> Fun (vecApp (getConstrName $ thry ^. sort) n) $ Fun linst sortExpr 
              ExtOpen n c -> Fun (vecApp c n) $ Fun linst sortExpr  

cpattern :: Name_ -> Name_ -> Term -> Constr -> [Pattern]
cpattern tinstName envName term c =
 let base = [IdP $ mkQName tinstName, mkPattern c]
     extBase i = (IdP $ mkQName i) : (IdP $ mkQName tinstName) : (IdP $ mkQName envName) : mkPattern c : []
 in case term of
    Basic -> base 
    (Closed _) -> base
    (Open n) -> extBase n
    (ExtOpen n _ ) -> extBase n
                
funcDef :: EqTheory -> Name_ -> Name_ -> Term -> Constr -> FunDefBody 
funcDef thry instName envName term constr = 
 let cexpr = applyProjConstr thry instName constr
     basicArgs = App [mkArg $ evalFuncName term, mkArg instName]
     extArgs i = App [mkArg $ evalFuncName term, mkArg i, mkArg instName, mkArg envName]
     funBody =
       case term of
        Basic -> functor' basicArgs cexpr 
        Closed _ -> functor' basicArgs cexpr 
        Open n -> functor' (extArgs n) cexpr 
        ExtOpen n _ -> functor' (extArgs n) cexpr 
  in FunDefBody funBody NoWhere 

lookup' :: Name_ -> Name_ -> FunDefBody
lookup' natVarName envName =
  FunDefBody (App [mkArg "lookup", mkArg natVarName, mkArg "x1", mkArg envName]) NoWhere

constFunc :: FunDefBody
constFunc =
    FunDefBody (App [mkArg "x1"]) NoWhere

oneEvalFunc :: EqTheory -> TermLang -> [Decl]
oneEvalFunc eq termLang@(TermLang term _ _ constrs) =
  let instName= twoCharName (eq ^. thyName) 0 
      envName = "vars"
      checkVar c = getConstrName c == v1 || getConstrName c == v2
      checkConstant c = getConstrName c == sing || getConstrName c == sing2
      vars = filter checkVar  constrs
      constants = filter checkConstant constrs
      fdecls = filter (\c -> not (checkVar c || checkConstant c)) constrs --  constrs \\ (vars `union` constants)
      funcs = eq ^. funcTypes 
  in 
  [TypeSig $ ftype eq termLang] ++
     (if vars == [] then [] 
      else [FunDef (mkName $ evalFuncName term) (concatMap (cpattern instName envName term) vars) (lookup' "n" envName)]) ++ 
     (if constants == [] then []
      else [FunDef (mkName $ evalFuncName term) (concatMap (cpattern instName envName term) constants) constFunc]) ++ 
     zipWith (FunDef (mkName $ evalFuncName term))
             (map (cpattern instName envName term) fdecls)
             (map (funcDef eq instName envName term) funcs)

evalFuncs :: EqTheory -> [TermLang] -> [Decl]
evalFuncs eq tlangs =
  concatMap (oneEvalFunc eq) tlangs 
