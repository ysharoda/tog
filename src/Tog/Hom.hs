{-# LANGUAGE OverloadedStrings #-}
module Hom where

import Tog.Raw.Abs

{-
Generating the homomorphism of single sorted theories of type Set.
- first, we classify the theory into sort, function symbols and axioms.
- At this point, we know there is one sort in the theories 
-} 

{-
data QName = Qual QName Name | NotQual Name
  deriving (Eq, Ord, Show, Read)
-} 
isSort :: Expr -> Bool
isSort expr =
  case expr of 
    Id (Qual _  (Name (_,"Set"))) -> True
    Id (NotQual (Name (_,"Set"))) -> True
    Eq  _ _  -> False
    Lam _ e  -> isSort e
    Pi  _ e  -> isSort e
    Fun e e' -> isSort e && isSort e'
    App args@((HArg _):_) -> and $ map (\(HArg a) -> isSort a) args
    App args@((Arg  _):_)  -> and $ map (\(Arg a) -> isSort a) args
    _ -> False 

isFunc :: Expr -> Bool
isFunc expr =
  case expr of
    App _   -> True
    Fun _ _ -> True 
    Pi  _ e -> isFunc e
    _       -> False

isAxiom :: Expr -> Bool
isAxiom expr =
  case expr of
    Eq _ _  -> True
    Lam _ e -> isAxiom e
    Pi  _ e -> isAxiom e
    Fun e e' -> isAxiom e && isAxiom e'
    App args@((HArg _):_) -> and $ map (\(HArg a) -> isAxiom a) args
    App args@((Arg  _):_) -> and $ map (\(Arg a)  -> isAxiom a) args 
    _  -> False

getName :: QName -> Name
getName (Qual _ n)  = n
getName (NotQual n) = n 

flattenBind :: Binding -> [Constr] 
flattenBind (Bind args e) =
  let flattenArg (Arg  (Id q)) = getName q
      flattenArg (HArg (Id q)) = getName q
      names = map flattenArg args
   in  map (\(n,t) -> Constr n t) $ zip names (take (length args) (repeat e))

flattenParams :: Params -> [Constr]
flattenParams NoParams       = []
flattenParams (ParamDef  _)  = []
flattenParams (ParamDecl bs) = concat $ map flattenBind bs

flattenRecordBody :: RecordBody -> [Constr]
flattenRecordBody (RecordDecl _) = []
flattenRecordBody (RecordDef _ NoFields) = [] 
flattenRecordBody (RecordDef _ (Fields l)) = l
flattenRecordBody (RecordDeclDef _ _ (Fields l)) = l
flattenRecordBody (RecordDeclDef _ _ NoFields) = []

fields :: Decl -> [Constr]
fields (Record _ params body) =
   flattenParams params ++ flattenRecordBody body   
-- TODO: Other Forms of Decl

{-
classify :: [Constr] -> ([Constr],[Constr],[Constr])
classify decls =
  let getExpr (Constr _ e) = e
      exprs  = map (\(Constr _ e) -> e) decls 
      sorts  = filter isSort exprs
      funcs  = filter isFunc exprs
      axioms = filter isAxiom exprs
 -}

    
