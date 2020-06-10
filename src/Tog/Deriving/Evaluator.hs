module Tog.Deriving.Evaluator where

import           Control.Lens ((^.))

-- import Tog.Deriving.TypeConversions
-- import Tog.Parse as P
-- import Tog.Deriving.Main
import Tog.Raw.Abs
import Tog.Deriving.EqTheory as Eq
import Tog.Deriving.Utils.QualDecls
import Tog.Deriving.TermLang --(termLangNm) 

import Tog.Deriving.Types (Name_)
import Tog.Deriving.TUtils
import Tog.Deriving.Utils.Parameters

evalFunNm :: String
evalFunNm = "evalTerm"

-- generates the type of the eval function 
-- lname: The name of the term langauge
-- instNm: The name of the instance of the theory given as input to the eval function 
ftype :: EqTheory -> Name_ -> Name_ -> TypeSig 
ftype thry lname instNm =
  let nm = thry ^. Eq.thyName
      a = args thry
      binds = map (genOneBinding HBind) a
  in Sig (mkName evalFunNm) $
      Pi (Tel $ if a == [] then [Bind [mkArg instNm] (App [mkArg nm])]  else binds) $ 
         Fun (declTheory nm (args thry) 0)
         $ Fun (App [mkArg lname])
           $ if (a == []) then qualDecl (getConstrName $ thry ^. sort) instNm
             else notQualDecl (getConstrName $ head a)
 
-- eval : {A : Set} -> Monoid A -> MonTerm -> A
-- eval : (M : Monoid) -> MonTerm -> (A M)
-- for every constr, we generate the two args needed for the function.
-- 1. The instance of the theory, for example Mo for  Monoid
-- 2. The pattern for the input constr 
mkPattern :: Name_ -> Constr -> [Pattern] 
mkPattern instName (Constr nm typ) =
  let arity = exprArity typ
      vars = genVars arity
      nameAppend (Name (l,n)) suff = Name (l,n ++ suff) 
      patt =
        if (arity == 0)
        then IdP (NotQual $ nameAppend nm termlangSuffix)
        else ConP (NotQual $ nameAppend nm termlangSuffix) $ map (\x -> IdP (NotQual $ mkName x)) vars 
  in [IdP (NotQual $ mkName instName) , patt] 

-- Generates the body of the function for one case
mkFunDef :: Name_ -> PConstr -> FunDefBody 
mkFunDef instNm pconstr@(PConstr _ typ _) = 
 FunDefBody (App $
   [Arg $ mkPExpr pconstr (instNm,0)] ++
    map (\x -> Arg $ App [mkArg evalFunNm, mkArg instNm ,mkArg x]) (genVars $ exprArity typ)) NoWhere 

evalFunc :: EqTheory -> [Decl]
evalFunc thry =
 let nm = thry ^. thyName
     instNm = twoCharName nm 0
     funcs = thry ^. funcTypes 
     (_,pfunc,_) = mkPConstrs thry
 in (TypeSig $ ftype thry (termLangNm thry) instNm) : 
     zipWith (FunDef (mkName evalFunNm)) (map (mkPattern instNm) funcs) (map (mkFunDef instNm) pfunc)

