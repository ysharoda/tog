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

predicateName :: String
predicateName = "P"

inducFuncNm :: Term -> String
inducFuncNm Basic         = "inductionB"
inducFuncNm (Closed _)    = "inductionCl"
inducFuncNm (BasicOpen _) = "inductionOpB"
inducFuncNm (Open _ _)    = "inductionOp" 

-- ----------------------------------------------------------------------------- 
-- the type signatures of the induction functions. 
typeSig :: TermLang -> TypeSig 
typeSig tl =
 let
  (_,binds,texpr) = tinstance (tlToDecl tl) Nothing
  fdecls = filter (not . isConstOrVar) (getTermConstructors tl)
  predApp = Pi (Tel [Bind [mkArg "x"] texpr]) (applyPred (App [mkArg "x"]))
 in Sig (mkName $ inducFuncNm $ getTermType tl) $ 
    Pi (Tel $ (map hiddenBind binds) ++ [HBind [mkArg predicateName] (Fun texpr setTypeExpr)]) $
      case getTermType tl of
        Basic -> curryExpr $ map typeFun fdecls ++ [predApp]
        Closed _ -> curryExpr $ typeSingleton sing : map typeFun fdecls ++ [predApp]
        BasicOpen _ -> curryExpr $ typeVar v1 : map typeFun fdecls ++ [predApp]
        Open _ _ -> curryExpr $ typeVar v2 : typeSingleton sing2 : map typeFun fdecls ++ [predApp]


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
applyPred (App [a]) = App $ mkArg predicateName : [a]
applyPred (App as) = App $ mkArg predicateName : [Arg $ App as]
applyPred (Id (NotQual x)) = App $ mkArg predicateName : [mkArg $ x ^. name]
applyPred _ = error "not a valid function application"

-- given a binding (\x1 x2 -> op x1 x2), construct [P x1, P x2] 
applyPredToBindings :: Binding -> [Expr]
applyPredToBindings (Bind as _) =
  map (\a -> App $ mkArg predicateName : [a]) as 
applyPredToBindings (HBind as e) =
  applyPredToBindings (Bind as e) 
  
-- (P e) → 
-- ({x y : MonTerm' n A} → P x → P y → P (op x y))     
typeFun :: Constr -> Expr
typeFun constr =
 let (b,fexpr) = fapp constr
     binds = map explicitBind b
 in if null binds then applyPred fexpr
    else Pi (Tel binds) $
         curryExpr $ concatMap applyPredToBindings binds ++ [applyPred fexpr]
-- -------------------------------------------------------------------------- 

predicateVar :: String
predicateVar = map toLower predicateName

patternName :: Name_ -> Name_
patternName n = map toLower (predicateName ++ n)

-- the patterns (inputs) for one function declaration 
patterns :: [Constr] -> [Pattern] 
patterns cs =
  map (IdP . mkQName . patternName . getConstrName) cs

-- the expression to be passed over in recursive calls 
recExpr :: Term -> [Constr] -> Expr 
recExpr term cs =
 App $
   (mkArg $ inducFuncNm term) :
   ((map mkArg $ implicit_ term) ++ 
     [mkArg $ "{"++predicateVar++"}"] ++ 
     (map mkArg $ map (patternName . getConstrName) cs))

implicit_ :: Term -> [String] 
implicit_ Basic = []
implicit_ (Closed _) = ["{_}"]
implicit_ (BasicOpen _) = ["{_}"]
implicit_ (Open _ _) = ["{_}","{_}"]
  
-- tog does not allow hidden arguments within the a type expression. For example, we cannot have the binding for x1 and x2 in the following definitions to be hidden. This means that we cannot have x1 and x2 be hidden as follows 
-- induction : ... -> ({x1 x2 : A} -> P x1 -> P x2 -> P (op x1 x2)) -> ..
-- as a consequence, the var corresponding to this proof will take 4 explicit arguments, not 2. We adjust the function calls by adding two _ _ for the two vars 
adjustFuncCalls :: Int -> Expr -> Expr
-- the given expression here is always a function application
adjustFuncCalls _ (Id x) = Id x
adjustFuncCalls n (App (a:as)) = App $ a : replicate n (mkArg "_") ++ as 
adjustFuncCalls _ _ = error "not a function application" 

adjustPattern :: TermLang -> Pattern -> [Pattern] 
adjustPattern (TermLang term _ _ tconstrs) p  =
  (map (\x -> IdP $ mkQName x) $ implicit_ term) ++ [IdP (mkQName $ "{"++predicateVar++"}")] ++ 
  patterns tconstrs ++ [p]
 
patternsExprs :: TermLang -> [(Pattern,Expr)]
patternsExprs (TermLang term _ _ tconstrs) =
  zipWith ((,)) (map mkPattern tconstrs)
                 (zipWith constrFunc [0 .. (length tconstrs)] tconstrs)
  where ps = patterns tconstrs 
        constrFunc i c@(Constr _ e)=
         let newConstr = Constr (mkName $ getPatternName (ps !! i)) e 
         in if (isConstOrVar c || farity e == 0) then fappExpr newConstr
            else adjustFuncCalls (farity e) $ functor' (recExpr term tconstrs) (fappExpr newConstr)
      
oneInducDef :: TermLang -> [Decl]
oneInducDef (TermLang _ _ _ []) = []
oneInducDef tl =
  TypeSig (typeSig tl) : 
  map (\(p,e) -> FunDef (mkName $ inducFuncNm term) (adjustPattern tl p) (mkFunDefBody e))
      (patternsExprs tl)
  where term = getTermType tl

inductionFuncs :: [TermLang] -> [Decl]
inductionFuncs tlangs = 
  concatMap oneInducDef tlangs
