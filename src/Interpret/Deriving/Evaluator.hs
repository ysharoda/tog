module Interpret.Deriving.Evaluator where

import Control.Lens ((^.))

import Tog.Raw.Abs hiding (Open)
import Interpret.Deriving.EqTheory as Eq
import Interpret.Deriving.Terms
import Interpret.Utils.Functions
import Interpret.Utils.Bindings (unionBindings)
import Interpret.Utils.TUtils

evalFuncName :: Term -> String
evalFuncName Basic         = "evalB"
evalFuncName (Closed _)    = "evalCl"
evalFuncName (BasicOpen _)      = "evalOpB"
evalFuncName (Open _ _) = "evalOp" 

envName :: String 
envName = "vars"

{-
1. the bindings for the term language + the bindings for the eq theory --> take their union
2. instance of monoid
3. instance of the term language
4. instance of Vec A n
5. Carrier
-}

-- the type signature for the evaluation function 
typeSig :: EqTheory -> TermLang -> TypeSig
typeSig thry termlang =
 let
   (instNm,eqbind,eqinst) = eqInstance thry Nothing
   (_,tbind,tinst) = tlangInstance termlang
   newBinds = unionBindings eqbind tbind
   sortExpr = projectConstr thry (instNm,eqbind,eqinst)  (thry ^. sort)
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
     extBase = [IdP $ mkQName tinstName, IdP $ mkQName envName, pat]
 in case term of
    Basic -> base 
    (Closed _) -> base
    (BasicOpen _) -> extBase
    (Open _ _ ) -> extBase
                
funcDef :: EqTheory -> Name_ -> Term -> Constr -> Expr  
funcDef thry instName term constr = 
 let (_,cexpr) = applyProjConstr thry (instName,[],Id (mkQName "x")) constr Nothing 
     basicArgs = App [mkArg $ evalFuncName term, mkArg instName]
     extArgs = App [mkArg $ evalFuncName term, mkArg instName, mkArg envName]
  in case term of
       Basic -> functor' basicArgs cexpr 
       Closed _ -> functor' basicArgs cexpr 
       BasicOpen _ -> functor' (extArgs) cexpr 
       Open _ _ -> functor' (extArgs) cexpr 
 
patternsExprs :: EqTheory -> TermLang -> Name_ -> [(Pattern,Expr)]
patternsExprs thry (TermLang term _ _ constrs) thryInstName =
  zipWith ((,)) (map mkPattern (vs ++ cs ++ typDecls)) $ 
                [lookup' envName | not (null vs)] 
                ++ [constFunc | not (null cs)] 
                ++ map (funcDef thry thryInstName term) thryDecls 
  where vs = filter isVarDecl  constrs
        cs = filter isConstDecl constrs
        thryDecls = (thry ^. funcTypes)
        typDecls  = filter (not . isConstOrVar) constrs

lookup' ::  Name_ -> Expr
lookup' vName  =
  App [mkArg "lookup", mkArg "_", mkArg "x1", mkArg vName]

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

evalFuncs :: EqTheory -> [TermLang] -> [Decl]
evalFuncs eq = concatMap (oneEvalFunc eq)

