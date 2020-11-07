module Tog.Deriving.StagedTerms where

import Tog.Raw.Abs hiding (Open)

import Tog.Deriving.Utils.Functions (farity)
import Tog.Deriving.Utils.Bindings (hiddenBind) 
import Tog.Deriving.Types (Name_)
import Tog.Deriving.TUtils (mkName, mkQName, mkArg, exprArity, genVars, getConstrName)
import Tog.Deriving.Lenses
import Tog.Deriving.Terms
import Tog.Deriving.Utils.Functions

import Control.Lens ((^.))

stagedFuncName :: Term -> String
stagedFuncName Basic         = "stageB"
stagedFuncName (Closed _)    = "stageCl"
stagedFuncName (BasicOpen _)      = "stageOpB"
stagedFuncName (Open _ _) = "stageOp" 

typeSig :: TermLang -> TypeSig 
typeSig tl =
 let (_,binds,texpr) = tlangInstance tl 
     stagedFuncTyp = Fun (texpr) (App [mkArg "Staged", Arg texpr])
 in Sig (mkName $ stagedFuncName $ getTermType tl) $
     if binds == [] then stagedFuncTyp
     else Pi (Tel binds) stagedFuncTyp

liftConstant :: Constr -> (Pattern,Expr) 
liftConstant c = (mkPattern c, App [mkArg "Now",Arg $ fappExpr c])

liftVariable :: Constr -> (Pattern,Expr)
liftVariable c =
  let vexp = App [mkArg (getConstrName c), mkArg "x1"]
  in (mkPattern c, App [mkArg "const", Arg $ App [mkArg "code",Arg $ vexp]])

-- -------------------------------------------------------------------------------- 
-- generate functions corresponding to the constructors of the term language 
opDeclToFuncName :: Name_ -> Name_
opDeclToFuncName cname = cname ++ "'"

opDeclToFunc :: TermLang -> Constr -> [Decl]
opDeclToFunc tl c@(Constr n expr) =
 let cname = n ^. name
     newname = opDeclToFuncName cname
     -- typName = getLangName tl 
     (_,binds,texpr) = tlangInstance tl  
 in (TypeSig $ Sig (mkName newname) $
     Pi (Tel (map hiddenBind binds)) $   
     curry' $ take (farity expr + 1) $ repeat (Arg $ texpr)) : 
    (FunDef (mkName newname) (map (IdP . mkQName) (genVars (exprArity expr))) $
      FunDefBody (fappExpr c) NoWhere) : []
-- -------------------------------------------------------------------------------- 

stage :: Term -> Constr -> Expr
stage term (Constr n expr) =
  let stageH fname liftF =
        App $ [mkArg fname,
              mkArg (opDeclToFuncName $ n^.name),
              Arg $ App [mkArg liftF, mkArg (opDeclToFuncName $ n^.name)]] ++
               map (liftExprType (App $ [mkArg $ stagedFuncName term] ++ underscoreArgs term)) (map mkArg $ genVars $ farity expr)
  in case exprArity expr of
   0 -> App [mkArg "Now",mkArg $ n ^. name]
   1 -> stageH "stage1" "codeLift1"
   2 -> stageH "stage2" "codeLift2"
   _ -> error "Cannot stage term, provide a staging function" 

liftFunc :: Term -> Constr -> (Pattern,Expr)
liftFunc term c =
  (mkPattern c, stage term c)

adjustPatterns :: TermLang -> Pattern -> [Pattern]
adjustPatterns tl p = underscorePattern (getTermType tl) ++ [p]

-- collecting patterns and expressions for all declarations
patternsExprs :: TermLang -> [(Pattern,Expr)]
patternsExprs tl = 
  let tconstrs = getTermConstructors tl
      constants = filter isConstDecl tconstrs
      variables = filter isVarDecl tconstrs 
      functions = filter (not . isConstOrVar) tconstrs
   in (map liftConstant constants) ++ (map liftVariable variables) ++ (map (liftFunc $ getTermType tl) functions)   

oneStagedFunc :: TermLang -> [Decl]
oneStagedFunc (TermLang _ _ _ []) = []
oneStagedFunc tl =
  let pe = patternsExprs tl
      tconstrs = getTermConstructors tl
      functions = filter (not . isConstOrVar) tconstrs
  in  (concatMap (opDeclToFunc tl)functions) ++ 
      ((TypeSig $ typeSig tl) :
       map (\(p,e) -> FunDef (mkName $ stagedFuncName (getTermType tl))
                             (adjustPatterns tl p)
                             (FunDefBody e  NoWhere)) pe)

stagedFuncs :: [TermLang] -> [Decl]
stagedFuncs langs =
  concatMap oneStagedFunc langs 
   
{-
liftAdditiveMonoidLang : AdditiveMonoidLang -> Staged AdditiveMonoidLang
liftAdditiveMonoidLang x = Now x

liftAdditiveMonoidLangCl : {A : Set} -> AdditiveMonoidLang A -> Staged (AdditiveMonoidLang A) 
liftAdditiveMonoidLang _ x = Now x

liftAdditiveMonoidOpenLang : (n : Nat) -> AdditiveMonoidOpenLang n -> Staged (AdditiveMonoidOpenLang n)
liftAdditiveMonoidOpenLang _ (v fin) = const _ (code _ (v fin))
liftAdditiveMonoidOpenLang _ (+OL x1 x2) =
  stage2 _ _ _ (+OL' _) (codeLift2 _ _ _ (+OL' _))
        (liftAdditiveMonoidOpenLang _ x1)
        (liftAdditiveMonoidOpenLang _ x2)
liftAdditiveMonoidOpenLang _ (0OL) = Now 0OL

-} 

