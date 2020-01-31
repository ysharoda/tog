{-# LANGUAGE TemplateHaskell #-}
module Tog.Utils where

import Control.Lens

import Tog.Raw.Abs 

isSort :: Expr -> Bool
isSort (Id (Qual _  (Name (_,"Set")))) = True
isSort (Id (NotQual (Name (_,"Set")))) = True
isSort (Lam _ e)  = isSort e
isSort (Pi _ e)   = isSort e
isSort (Fun e e') = isSort e && isSort e'
isSort (App args@((HArg _):_)) = and $ map (\(HArg a) -> isSort a) args
isSort (App args@((Arg  _):_)) = and $ map (\(Arg a) -> isSort a) args
isSort (Eq _ _) = False
isSort _ = False 

isFunc :: Expr -> Bool
isFunc (Id (NotQual (Name (_,"Set")))) = False
isFunc (Id (NotQual (Name (_,_))))     = True
isFunc (Id (Qual _  (Name (_,"Set")))) = False
isFunc (Id (Qual _  (Name (_,_))))     = True
isFunc (App args@((Arg  _):_))  = and $ map (\(Arg a)  -> isFunc a) args
isFunc (App args@((HArg  _):_)) = and $ map (\(HArg a) -> isFunc a) args
isFunc (Fun e1 e2) = isFunc e1 && isFunc e2
isFunc (Pi _ e)    = isFunc e
isFunc _ = False 

isAxiom :: Expr -> Bool
isAxiom (Eq _ _) = True
isAxiom (Lam _ e) = isAxiom e
isAxiom (Pi _ e)  = isAxiom e
isAxiom (Fun e e') = isAxiom e && isAxiom e'
isAxiom (App args@((HArg _):_)) = and $ map (\(HArg a) -> isAxiom a) args
isAxiom (App args@((Arg  _):_)) = and $ map (\(Arg a)  -> isAxiom a) args
isAxiom _ = False 

getExpr :: Constr -> Expr
getExpr (Constr _ e) = e 

liftFilter :: (Expr -> Bool) -> [Constr] -> [Constr] 
liftFilter p l = [c | c <- l, p $ getExpr c] 

classify :: [Constr] -> ([Constr],[Constr],[Constr])
classify constrs = classify' constrs ([],[],[])
 where classify' [] tuple = tuple 
       classify' (c:cs) (sorts,funcs,axioms) = 
         if isSort (getExpr c)       then classify' cs (c:sorts,funcs,axioms)
         else if isFunc (getExpr c)  then classify' cs (sorts,c:funcs,axioms)
         else if isAxiom (getExpr c) then classify' cs (sorts,funcs,c:axioms)
         else error "Cannot classify declaration."

nameToStr :: Name -> String
nameToStr (Name (_,n)) = n 

qnameToStr :: QName -> String
qnameToStr (NotQual name) = nameToStr name 
qnameToStr (Qual q  name) = qnameToStr q ++ "." ++ nameToStr name              

createIdNQ :: String -> Expr
createIdNQ str = Id $ NotQual $ Name ((0,0),str)

strToArg :: String -> Arg 
strToArg str = Arg $ createIdNQ str

nameStr :: Name -> String 
nameStr (Name (_,n)) = n


{- ------------------------------------------------------------ -} 
{- ---------------------- Getters ----------------------------- -} 
{- ------------------------------------------------------------ -} 

makePrisms ''Name 
makePrisms ''QName  
makePrisms ''Arg
makePrisms ''Binding
makePrisms ''Expr

getName :: Name -> Maybe String 
getName n = n ^? _Name._2

getQname :: QName -> Maybe String 
getQname (Qual q n)  = (++) <$> getQname q <*> getName n
getQname qn = qn ^? _NotQual.to getName._Just 
-- (++) <$> ((++) <$> qname q <*> pure ".") <*> name n 

getArgName :: Arg -> Maybe String 
getArgName arg@(Arg  _) = arg ^? _Arg._Id.to getQname._Just 
getArgName arg@(HArg _) = arg ^? _HArg._Id.to getQname._Just

getRecordName :: Decl -> Maybe String 
getRecordName (Record name _ _) = getName name
getRecordName _ = Nothing

getParams :: Params -> [Binding]
getParams (ParamDecl bs) = bs
getParams _ = []

getFields :: Fields -> [Constr] 
getFields NoFields = []
getFields (Fields ls) = ls 


{- ------------------------------------------------------------ -} 
{- ------------------ Rename Functions ------------------------ -} 
{- ------------------------------------------------------------ -} 

setName :: String -> String -> Name -> Name 
setName oldName newName n = 
  if getName n == Just oldName 
  then n & _Name._2 .~ newName 
  else n 

-- In case of a qualified name, only the last part of it is renamed. 
setQname :: String -> String -> QName -> QName 
setQname oldName newName (NotQual name) = NotQual $ setName oldName newName name 
setQname oldName newName (Qual qn name) = Qual qn $ setName oldName newName name 
-- qn & _Qual._2._Name._2 .~ newName 

renameArg :: String -> String -> Arg -> Arg  
renameArg oldName newName (Arg  expr) = Arg  $ renameExpr oldName newName expr
renameArg oldName newName (HArg expr) = HArg $ renameExpr oldName newName expr
-- arg & _Arg._Id._NotQual._Name._2 .~ newName 

renameBinding :: String -> String -> Binding -> Binding 
renameBinding oldName newName (Bind args expr) 
   = Bind  (map (renameArg oldName newName) args) (renameExpr oldName newName expr)
renameBinding oldName newName (HBind args expr) 
   = HBind (map (renameArg oldName newName) args) (renameExpr oldName newName expr)

getBindingArgs :: Binding -> [Arg]
getBindingArgs (Bind  args _) = args
getBindingArgs (HBind args _) = args 

getBindingExpr :: Binding -> Expr
getBindingExpr (Bind  _ expr) = expr
getBindingExpr (HBind _ expr) = expr

data Flag = Hide | Explicit deriving Eq

mergeBindings :: Flag -> Binding -> Binding -> [Binding]
mergeBindings f b1 b2 =
  let merge = getBindingExpr b1 == getBindingExpr b2
      mergedArgs = (getBindingArgs b1 ++ getBindingArgs b2)
      hide  = (f == Hide) 
   in case (merge,hide) of
    (True,True)  -> [HBind mergedArgs (getBindingExpr b1)]
    (True,False) -> [Bind  mergedArgs (getBindingExpr b1)]
    (False,_)    -> [b1,b2]

renameExpr :: String -> String -> Expr -> Expr 
renameExpr oldName newName ex =
  case ex of
    Lam names expr      -> Lam (map (setName oldName newName) names) (renExpr expr)
    Pi (Tel binds) expr -> Pi (Tel $ map (renameBinding oldName newName) binds) (renExpr expr)
    Fun expr1 expr2     -> Fun (renExpr expr1) (renExpr expr2) 
    Eq  expr1 expr2     -> Eq  (renExpr expr1) (renExpr expr2) 
    App args            -> App $ map (renameArg oldName newName) args   
    Id  qn              -> Id  $ setQname oldName newName qn
  where renExpr = renameExpr oldName newName 
