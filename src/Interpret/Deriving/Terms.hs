module Interpret.Deriving.Terms where

import Tog.Raw.Abs hiding (Open) 
import Interpret.Flattener.Types (gmap)
import Interpret.Utils.Functions (liftType')
import Interpret.Utils.Renames (foldren)
import Interpret.Utils.Types (tinstance)
import Interpret.Utils.TUtils (Name_, mkName, mkQName, mkArg, setType, getConstrName)
import Interpret.Deriving.EqTheory
import Interpret.Utils.Lenses (name)

import Control.Lens ((^.))
import Data.Map as Map (Map,fromList, toList) 


-- The definition of closed term lang is parameterized by the name of the carrier
-- The definition of an open term lang is parameterized by the name of a variable of type `Nat`
-- The definition of an extended term lang is parameterized by both. 
type NumOfVars = Name_
type CarrierName = Name_ 

data Term = Basic
          | Closed CarrierName
          | BasicOpen NumOfVars
          | Open NumOfVars CarrierName deriving (Eq,Show)

data TermLang = TermLang {
  termTy  :: Term,
  tname   :: Name_,
  params  :: Params,
  cons    :: [Constr] } deriving Show

getTermType :: TermLang -> Term
getTermType (TermLang ty _ _ _) = ty

getTermConstructors :: TermLang -> [Constr]
getTermConstructors (TermLang _ _ _ cs) = cs

getLangName :: TermLang -> Name_
getLangName (TermLang _ n _ _) = n

-- Utils 
isVarDecl :: Constr -> Bool
isVarDecl c = getConstrName c == v1 || getConstrName c == v2

isConstDecl :: Constr -> Bool
isConstDecl c = getConstrName c == sing || getConstrName c == sing2

isConstOrVar :: Constr -> Bool
isConstOrVar c = isVarDecl c || isConstDecl c

tlToDecl :: TermLang -> Decl
tlToDecl (TermLang _ nm pars constrs) =
 Data (mkName nm) pars (DataDeclDef setType constrs)

tlangInstance :: TermLang -> (Name_,[Binding],Expr)
tlangInstance tl = tinstance (tlToDecl tl) Nothing  

-- step1: rename all constrs of the thoery
v1,v2, sing, sing2 :: String
v1 = "v"
v2 = "v2"
sing = "sing"
sing2 = "sing2"

mapping :: EqTheory -> Term -> Map Name_ Name_
mapping eq Basic = mappingHelper eq "L"
mapping eq (Closed _) = mappingHelper eq "Cl"
mapping eq (BasicOpen _) = mappingHelper eq "OL"
mapping eq (Open _ _) = mappingHelper eq "OL2"

mappingHelper :: EqTheory -> String ->  Map Name_ Name_
mappingHelper eq suffix =
  let names = map (\(Constr n _) -> n ^. name) (eq ^. funcTypes) 
  in Map.fromList (zip names (map (++ suffix) names))

-- step2: the name of the new type
declName :: Name_ -> Term -> Name_
declName nm Basic = nm ++ "Term"
declName nm (Closed _) = "Cl" ++ nm ++ "Term"
declName nm (BasicOpen _) = "Op" ++ nm ++ "Term"
declName nm (Open _ _) = "Op" ++ nm ++ "Term2"

-- step3: construct the type of terms in each case
termType :: Name_ -> Term -> Expr
termType thryNm Basic = App [liftType' (declName thryNm Basic) []]
termType thryNm t@(Closed carrierNm) = App [liftType' (declName thryNm t) [mkArg carrierNm]]
termType thryNm t@(BasicOpen natVarNm) = App [liftType' (declName thryNm t) [mkArg natVarNm]]
termType thryNm t@(Open natVarNm carrierNm) =
  App [liftType' (declName thryNm t) $ map mkArg [natVarNm, carrierNm]]

-- step 4: construct the declaration

mkParams :: Term -> Params
mkParams Basic = mkParamsHelper []
mkParams (Closed carrierNm) = mkParamsHelper [(carrierNm,App [mkArg "Set"])]
mkParams (BasicOpen natVarNm) = mkParamsHelper [(natVarNm,Id (mkQName "Nat"))]
mkParams (Open natVarNm carrierNm) =
  mkParamsHelper [(natVarNm,App [mkArg "Nat"]),(carrierNm,App [mkArg "Set"])]

mkParamsHelper :: [(Name_,Expr)] -> Params
mkParamsHelper [] = NoParams
mkParamsHelper xs = ParamDecl $ map (\(n,e) -> (Bind [mkArg n] e)) xs

constructors :: Term -> Name_ -> [Constr] -> [Constr]
constructors t thryNm fsyms =
 let typ = termType thryNm t
     constrs = map (constructorsHelper $ termType thryNm t) fsyms
 in case t of
   Basic -> constrs
   (Closed carrierNm) -> (singleton sing carrierNm typ) : constrs
   (BasicOpen natVarNm) -> (vars v1 natVarNm typ) : constrs
   (Open natVarNm carrierNm) -> (vars v2 natVarNm typ) : (singleton "sing2" carrierNm typ) : constrs 

constructorsHelper :: Expr -> Constr -> Constr
constructorsHelper (App as) c = gmap (\_ -> as) c
constructorsHelper _ _ = error "invalid type"

singleton :: Name_ -> Name_ -> Expr -> Constr 
singleton singConstrNm carrierNm declType =
  Constr (mkName singConstrNm)
    (Fun (App [mkArg carrierNm]) declType)

vars :: Name_ -> Name_ -> Expr -> Constr
vars vconstrNm natVarNm expr =
 let fin = App [mkArg "Fin", mkArg natVarNm]
 in Constr (mkName vconstrNm) (Fun fin expr) 

{-
data TermLang = TermLang {
  term    :: Term,
  name    :: Name_,
  params  :: Params
  constrs :: [Constr] }
-}

tlang :: EqTheory -> Term -> TermLang
tlang eq term =
 let neq = foldren eq $ Map.toList (mapping eq term) 
 in TermLang term (declName (neq ^. thyName) term) (mkParams term) $
       constructors term  (neq ^. thyName) (neq ^. funcTypes)

termLangs :: EqTheory -> [TermLang]
termLangs eq = 
 let nm = getConstrName $ eq ^. sort
 in map (tlang eq) [Basic, Closed nm, BasicOpen "n", Open "n" nm]

    
decl :: EqTheory -> Term -> Decl 
decl eq term  =
 let neq = foldren eq $ Map.toList (mapping eq term) 
 in Data (mkName $ declName (neq ^. thyName) term) (mkParams term) $
     DataDeclDef setType $ constructors term  (neq ^. thyName) (neq ^. funcTypes) 

termLangsToDecls :: [TermLang] -> [Decl]
termLangsToDecls tls = map tlToDecl tls 
  
{-

e : A
e : MonTerm
e : MonTerm A
e : MonTerm n
e : MonTerm n A 

data MonTerm : Set where
 e : MonTerm
 op : MonTerm -> MonTerm -> MonTerm

data MonTerm (A : Set) where
 singleton : A -> MonTerm A
 e : MonTerm A
 op : MonTerm A -> MonTerm n A -> MonTerm n A

data MonTerm (n : ℕ) : Set where
 v : (Fin n) -> MonTerm n
 e : MonTerm' n
 op : MonTerm' n -> MonTerm' n -> MonTerm' n


data MonTerm' (n : ℕ) (A : Set) : Set where 
 singleton : A -> MonTerm' n A
 v : (Fin n) -> MonTerm' n A
 e : MonTerm' n A
 op : MonTerm' n A -> MonTerm' n A -> MonTerm' n A 

-} 

-- extra utils functions
-- ---- to get around the hidden arguments problem ----------------- 
{-
underscorePattern :: Term -> [Pattern]
underscorePattern Basic = []
underscorePattern (Closed _) = [IdP $ mkQName "_"]
underscorePattern (BasicOpen _) = [IdP $ mkQName "_"]
underscorePattern (Open _ _) = take 2 $ repeat (IdP $ mkQName "_") 

underscoreArgs :: Term -> [Arg]
underscoreArgs Basic = []
underscoreArgs (Closed _) = [mkArg "_"] 
underscoreArgs (BasicOpen _)   = [mkArg "_"]
underscoreArgs (Open _ _) = [mkArg "_",mkArg "_"] 
-}
