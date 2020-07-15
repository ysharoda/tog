module Tog.Deriving.Induction where

import Tog.Raw.Abs hiding (Open)
import Tog.Deriving.Terms
import Tog.Deriving.EqTheory
import Tog.Deriving.TUtils 
import Tog.Deriving.Utils.Functions
import Tog.Deriving.Utils.Bindings
import Tog.Deriving.Utils.Types

import Tog.Deriving.Lenses (name)
import Control.Lens ((^.))
{-
induction : (P : MonTerm -> Set) -> P ee -> ((x y : MonTerm) -> P x -> P y -> P (opp x y)) -> ((x : MonTerm) -> P x)

monoid_ind
     : forall P : monoid -> Prop,
       P e' ->
       (forall m : monoid, P m -> forall m0 : monoid, P m0 -> P (op' m m0)) ->
       forall m : monoid, P m
monoidCl_ind
     : forall (A : Set) (P : monoidCl A -> Prop),
       (forall a : A, P (singleton' A a)) ->
       P (eCl' A) ->
       (forall m : monoidCl A,
        P m -> forall m0 : monoidCl A, P m0 -> P (opCl' A m m0)) ->
       forall m : monoidCl A, P m
monoidOp_ind
     : forall (n : nat) (P : monoidOp n -> Prop),
       (forall t : Fin.t n, P (v' n t)) ->
       P (eOp' n) ->
       (forall m : monoidOp n,
        P m -> forall m0 : monoidOp n, P m0 -> P (opOp' n m m0)) ->
       forall m : monoidOp n, P m
monoidOpExt_ind
     : forall (n : nat) (A : Set) (P : monoidOpExt n A -> Prop),
       (forall t : Fin.t n, P (vOpE' n A t)) ->
       (forall a : A, P (singletonOpE' n A a)) ->
       P (eOpE' n A) ->
       (forall m : monoidOpExt n A,
        P m -> forall m0 : monoidOpExt n A, P m0 -> P (opOpE' n A m m0)) ->
       forall m : monoidOpExt n A, P m
-}

predicateName :: String
predicateName = "P"

inducFuncNm :: Term -> String
inducFuncNm Basic         = "inductionB"
inducFuncNm (Closed _)    = "inductionCl"
inducFuncNm (Open _)      = "inductionOp"
inducFuncNm (ExtOpen _ _) = "inductionOpE" 


-- ({fin : Fin n} → P (v fin))
typeVar :: String -> Expr
typeVar varConstrName =
  Pi (Tel [HBind [mkArg "fin"] (App [mkArg "Fin",mkArg "n"])]) $
     App [mkArg predicateName,
          Arg $ App [mkArg varConstrName, mkArg "fin"]]

-- ({x : A} → P (singleton x))     
typeSingleton :: String -> Expr
typeSingleton constantConstrName =
  Pi (Tel [HBind [mkArg "x1"] $ App [mkArg "A"]]) $
     App [mkArg predicateName,
          Arg $ App [mkArg constantConstrName, mkArg "x1"]]

-- given an expression e, construct P e 
applyPred :: Expr -> Expr
applyPred (App as) = App $ (mkArg predicateName) : [Arg $ App as]
applyPred (App [a]) = App $ (mkArg predicateName) : [a]
applyPred (Id (NotQual x)) = App $ (mkArg predicateName) : [mkArg $ x ^. name]
applyPred _ = error "not a valid function application"

-- given a binding (\x1 x2 -> op x1 x2), construct [P x1, P x2] 
applyPredToBindings :: Binding -> [Expr]
applyPredToBindings (Bind as _) =
  map (\a -> App $ (mkArg predicateName) : [a]) as 
applyPredToBindings (HBind as e) =
  applyPredToBindings (Bind as e) 
  
-- (P e) → 
-- ({x y : MonTerm' n A} → P x → P y → P (op x y))     
typeFun :: Constr -> Expr
typeFun constr =
 let (FApp binds fexpr) = fapp constr
 in if binds == [] then applyPred fexpr
    else Pi (Tel binds) $
         curryExpr $ (concatMap applyPredToBindings binds) ++ [applyPred fexpr]
{-
inductionOpE : {A : Set} {n : ℕ} → (P : MonTerm' n A → Set) →
          ({fin : Fin n} → P (v fin)) →
          ({x : A} → P (singleton x)) →
          (P e) → 
          ({x y : MonTerm' n A} → P x → P y → P (op x y)) → ((x : MonTerm' n A) → P x)
-} 
typeSig :: EqTheory -> TermLang -> TypeSig 
typeSig eq tlang =
 let
  (DTApp binds texpr) = tapp (tlToDecl tlang) Nothing
  check c = (getConstrName c == v1 || getConstrName c == v2 || getConstrName c == sing || getConstrName c == sing2)
  fdecls = filter (not . check) (getTermConstructors tlang)
  pred = Pi (Tel [Bind [mkArg "x"] texpr]) (applyPred (App [mkArg "x"]))
 in Sig (mkName $ inducFuncNm $ getTermType tlang) $ 
    Pi (Tel $ binds ++ [Bind [mkArg predicateName] (Fun texpr setTypeExpr)]) $
      case getTermType tlang of
        Basic -> curryExpr $ (map typeFun fdecls) ++ [pred]
        Closed _ -> curryExpr $ (typeSingleton sing) : (map typeFun fdecls) ++ [pred]
        Open _ -> curryExpr $ (typeVar v1) : (map typeFun fdecls) ++ [pred]
        ExtOpen _ _ -> curryExpr $ (typeSingleton sing2) : (typeVar v2) : (map typeFun fdecls) ++ [pred]
     

 
{-
 induction : (P : MonTerm -> Set) -> P ee -> ((x y : MonTerm) -> P x -> P y -> P (opp x y)) -> ((x : MonTerm) -> P x)
 induction p pe _ ee = pe
 induction p pe f (opp e1 e2) = f _ _ (induction p pe f e1) (induction p pe f e2)



-} 


-- evaluator, simplifier and staged terms should depend on term types, not theories. 
