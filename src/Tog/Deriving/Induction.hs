module Tog.Deriving.Induction where

import Tog.Raw.Abs hiding (Open)
import Tog.Deriving.Terms
import Tog.Deriving.TUtils 
import Tog.Deriving.Utils.Functions
import Tog.Deriving.Utils.Bindings
import Tog.Deriving.Utils.Types
import Tog.Deriving.Types  (Name_)

import Tog.Deriving.Lenses (name)
import Control.Lens ((^.))
import Data.Char (toLower) 
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
  Pi (Tel [Bind [mkArg "fin"] (App [mkArg "Fin",mkArg "n"])]) $
     App [mkArg predicateName,
          Arg $ App [mkArg varConstrName, mkArg "fin"]]

-- ({x : A} → P (singleton x))     
typeSingleton :: String -> Expr
typeSingleton constantConstrName =
  Pi (Tel [Bind [mkArg "x1"] $ App [mkArg "A"]]) $
     App [mkArg predicateName,
          Arg $ App [mkArg constantConstrName, mkArg "x1"]]

-- given an expression e, construct P e 
applyPred :: Expr -> Expr
applyPred (App [a]) = App $ (mkArg predicateName) : [a]
applyPred (App as) = App $ (mkArg predicateName) : [Arg $ App as]
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
 let (FApp b fexpr) = fapp constr
     binds = map explicitBind b
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
typeSig :: TermLang -> TypeSig 
typeSig tl =
 let
  (DTApp binds texpr) = tapp (tlToDecl tl) Nothing
  check c = (getConstrName c == v1 || getConstrName c == v2 || getConstrName c == sing || getConstrName c == sing2)
  fdecls = filter (not . check) (getTermConstructors tl)
  predApp = Pi (Tel [Bind [mkArg "x"] texpr]) (applyPred (App [mkArg "x"]))
 in Sig (mkName $ inducFuncNm $ getTermType tl) $ 
    Pi (Tel $ binds ++ [Bind [mkArg predicateName] (Fun texpr setTypeExpr)]) $
      case getTermType tl of
        Basic -> curryExpr $ (map typeFun fdecls) ++ [predApp]
        Closed _ -> curryExpr $ (typeSingleton sing) : (map typeFun fdecls) ++ [predApp]
        Open _ -> curryExpr $ (typeVar v1) : (map typeFun fdecls) ++ [predApp]
        ExtOpen _ _ -> curryExpr $ (typeVar v2) : (typeSingleton sing2) : (map typeFun fdecls) ++ [predApp]

      {-
fdecl :: Constr -> (Pattern, FunDefBody)
fdecl constr =
 let pattern  
  (mkPattern constr,
   FunDefBody (fappExpr constr) NoWhere)
-}

predicateVar :: String
predicateVar = map toLower predicateName

patternName :: Name_ -> Name_
patternName n = map toLower (predicateName ++ n)

-- the patterns for one function declaration 
patterns :: [Constr] -> [Pattern] 
patterns cs =
  [IdP $ mkQName predicateVar] ++ map (IdP . mkQName . patternName . getConstrName) cs

-- the expression to be passed over in recursive calls 
recExpr :: Term -> [Constr] -> Expr 
recExpr term cs =
 App $
   [mkArg $ inducFuncNm term] ++ underscoreArgs term ++ (map mkArg $ [predicateVar] ++ (map (patternName . getConstrName) cs)) 
  
-- tog does not allow hidden arguments within the a type expression. For example, we cannot have the binding for x1 and x2 in the following definitions to be hidden. This means that we cannot have x1 and x2 be hidden as follows 
-- induction : ... -> ({x1 x2 : A} -> P x1 -> P x2 -> P (op x1 x2)) -> ..
-- as a consequence, the var corresponding to this proof will take 4 explicit arguments, not 2. We adjust the function calls by adding two _ _ for the two vars 
adjustFuncCalls :: Int -> Expr -> Expr
-- the given expression here is always a function application
adjustFuncCalls _ (Id x) = Id x
adjustFuncCalls n (App (a:as)) = App $ a : (take n $ repeat (mkArg "_")) ++ as 
adjustFuncCalls _ _ = error "not a function application" 

  
oneInducDef :: TermLang -> [Decl]
oneInducDef tl =
 let tconstrs = getTermConstructors tl
  --   constantDecl = filter (getConstrName c == sing || getConstrName c == sing2) constructors
     ttyp = getTermType tl
     constrPatterns = patterns tconstrs
     check c = (getConstrName c == v1 || getConstrName c == v2 || getConstrName c == sing || getConstrName c == sing2)
     constrFunc index c@(Constr _ e) =
       let pName = getPatternName $ constrPatterns !! index
           newConstr = Constr (mkName $ pName) e 
       in if check c || farity e == 0 then fappExpr newConstr
          else adjustFuncCalls (farity e) $ functor' (recExpr ttyp tconstrs) (fappExpr newConstr)
     mkDecl i c =
       FunDef (mkName $ inducFuncNm ttyp)
        (underscorePattern ttyp ++ constrPatterns ++ [mkPattern c])
        (FunDefBody (constrFunc i c) NoWhere)
 in (TypeSig $ typeSig tl) : zipWith mkDecl [1 .. (length tconstrs)] tconstrs

inductionFuncs :: [TermLang] -> [Decl]
inductionFuncs tlangs = 
  concatMap oneInducDef tlangs
