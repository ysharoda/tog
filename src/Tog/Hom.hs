module Tog.Hom where

{-
 - Generating Homomorphism definitions for single-sorted 
 -} 

import Tog.Raw.Abs
import Tog.Parse
import Tog.ScopeCheck 
import Data.Functor
import Tog.Utils 

-- Dummy location to pass to Name instances. 
loc :: (Int,Int)
loc = (0,0)

suffix1 :: String
suffix1 = "1"
suffix2 :: String 
suffix2 = "2"
instanceName :: String
instanceName = "inst"
homFuncName :: String 
homFuncName = "hom"

homRecordName :: Name -> Name
homRecordName (Name (_,n)) = Name (loc,n++"Hom") 

createIdNQ :: String -> Expr
createIdNQ str = Id $ NotQual $ Name (loc,str)

-- instantiate an argument
instantiateArg :: String -> Arg -> Arg
instantiateArg str arg =
  let getExpr (Arg e)  = e
      getExpr (HArg e) = e
      modifyExpr e =
        case e of
          Id  qname  -> Arg $ createIdNQ $ qnameToStr qname ++ str
          App (a:as) -> modifyExpr $ getExpr a
          e'         -> error $ "Invalid argument" ++ show e
  in modifyExpr $ getExpr arg 

-- one argument as a binding
instanceArgs :: [Binding] -> String -> [Arg]
instanceArgs []     _   = [] 
instanceArgs (b:bs) str =
  map (instantiateArg str) $ arguments b
   ++ instanceArgs bs str
  where
    arguments (Bind  a _) = a
    arguments (HBind a _) = a

{- The arguments to the record becomes hidden arguments to hom.
 - For example, an argument (A : Set) in the input record,
 - triggers the generation of two hidden arguments {A1 A2 : Set}
 -}
createHiddenBindings :: Binding -> Binding
createHiddenBindings binding =
  case binding of
    HBind args e -> HBind (newargs args) e
    Bind  args e -> HBind (newargs args) e
  where duplicateArg arg =
             [instantiateArg suffix1 arg] ++ [instantiateArg suffix2 arg] 
        newargs args_list = concat $ map duplicateArg args_list 


instantiateRecord :: Name -> [Binding]-> String -> Binding
instantiateRecord (Name (_,n)) bindings index =
  Bind [Arg $ createIdNQ $ instanceName ++ index]
       (App $ [Arg $ createIdNQ n] ++ inst)
  where inst = instanceArgs bindings index

createHomParam :: Name -> Params -> Params
createHomParam n NoParams     = NoParams
createHomParam n (ParamDef _) = NoParams -- ??
createHomParam n (ParamDecl bindings) =
  ParamDecl $ (map createHiddenBindings bindings)
              ++ [instantiateRecord n bindings suffix1]
              ++ [instantiateRecord n bindings suffix2]

{- create the Hom declarations -}




createHomFunc :: Constr -> Constr
createHomFunc c@(Constr (Name (_,n)) e) =
  Constr (Name ((5,5),homFuncName))
         (Fun (name suffix1)
              (name suffix2))
   where name str = App [Arg (createIdNQ (n ++ str))]

arity :: Expr -> Int
arity expr =
  let count e = 
       case e of
         Fun e1 e2      -> (count e1) + (count e2)
         App argslist   -> length argslist
         Id  _          -> 1
         Lam names _    -> length names
         Pi (Tel bs) e' -> length bs + count e'
         Eq  _  _       -> error "Not a function"
   in count expr -1 

genVars i = zipWith (++) (take i $ repeat "x") $ map show [1..i]

genBind :: Expr -> [Binding]
genBind expr =
  let args  = map (\x -> Arg $ createIdNQ x) $ genVars $ arity expr
      rename (Arg (Id (NotQual (Name (l,n))))) =
             (Arg (Id (NotQual (Name (l,n++suffix1)))))
      types e =
        case e of
          App arg   -> [App (map rename arg)]
          Fun e1 e2 -> (types e1) ++ (types e2)
          _         -> error "invalid expression"
   in zipWith (\v ty -> HBind [v] ty) args (types expr)

genHomFuncApp :: Constr -> Name -> Expr
genHomFuncApp constr inst =
  App $ [strToArg homFuncName] ++ genHomFuncArg constr inst

genHomFuncArg :: Constr -> Name -> [Arg]
genHomFuncArg (Constr name expr) inst =
  -- qualifying by the instance name  
  let funcName = App [strToArg (nameToStr name), strToArg (nameToStr inst)] 
      vars  = map (\x -> createIdNQ x) $ genVars $ arity expr
   in case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> map Arg $ funcName:vars
       Fun _ _  -> [Arg $ App $ map Arg $ funcName:vars] 

genLHS :: Constr -> Name -> Expr
genLHS constr inst = genHomFuncApp constr inst

genRHS :: Constr -> Name -> Expr
genRHS (Constr name expr) inst =
  let funcName = App [strToArg (nameToStr name), strToArg (nameToStr inst)]
      vars  = map (\x -> createIdNQ x) $ genVars $ arity expr
      args e = 
        case e of
          Id qname    -> genHomFuncApp (Constr (Name ((6,6),"dummy")) (Id qname)) inst
      --    App [Arg a] -> args a 
      --    App (a:as)  -> args (App [a]) ++ (args $ App as)
      --    Fun e1 e2   -> args e1 ++ args e2
  in App $ map Arg $ funcName:(map args vars)

genEq :: Constr -> Expr
genEq constr =
  let inst1 = Name ((7,7),instanceName ++ suffix1)
      inst2 = Name ((8,8),instanceName ++ suffix2)
  in  Eq (genLHS constr inst1)
         (genRHS constr inst2)

createPresAxioms :: Constr -> Constr
createPresAxioms c@(Constr (Name (_,op)) e) =
  let name = "pres-" ++ op
      binding = genBind e
      -- vars = map (\x -> Arg $ createNotQualId x) $ genVars $ arity expr
  in Constr (Name (loc,name))
            (Pi (Tel binding) (genEq c)) 

createHomBody :: [Constr] -> [Constr]
createHomBody clist =
  map createHomFunc (liftFilter isSort clist) ++
  map createPresAxioms (liftFilter isFunc clist) 

createHom :: Decl -> Decl
createHom (Record name params body) =
  Record (homRecordName name) 
         (createHomParam name params)
         (RecordDeclDef (Name (loc,"Set"))
                        (Name (loc,"rechom"))
                        (Fields $ createHomBody $ (getConstr body) ++ (paramsToFields params)))
  where getConstr (RecordDecl _) = []
        getConstr (RecordDef _ NoFields) = []
        getConstr (RecordDef _ (Fields c)) = c
        getConstr (RecordDeclDef _ _ NoFields) = []
        getConstr (RecordDeclDef _ _ (Fields c)) = c 


appendToModule :: Module -> [Decl] -> Module
appendToModule (Module n p decls) moreDecls = Module n p (decls ++ moreDecls)

readModuleRecords :: Module -> [Decl]
readModuleRecords (Module _ _ decls) = readRecords decls 

paramsToFields :: Params -> [Constr]
paramsToFields NoParams       = []
paramsToFields (ParamDef  _)  = []
paramsToFields (ParamDecl bs) =
  concat $ map flattenBind bs
  where getName :: QName -> Name
        getName (Qual _ n)  = n
        getName (NotQual n) = n 
        flattenBind :: Binding -> [Constr] 
        flattenBind (Bind args e) =
           let flattenArg (Arg  (Id q)) = getName q
               flattenArg (HArg (Id q)) = getName q
               names = map flattenArg args
           in  map (\(n,t) -> Constr n t) $ zip names (take (length args) (repeat e))

{- Testing -} 
-- Given all declarations in the file, we filter the records 
readRecords :: [Decl] -> [Decl]
readRecords ((Record n p r):decls) = (Record n p r) : readRecords decls
readRecords (_:decls) = readRecords decls
readRecords [] = []

flattenRecordBody :: RecordBody -> [Constr]
flattenRecordBody (RecordDecl _) = []
flattenRecordBody (RecordDef _ NoFields) = [] 
flattenRecordBody (RecordDef _ (Fields l)) = l
flattenRecordBody (RecordDeclDef _ _ (Fields l)) = l
flattenRecordBody (RecordDeclDef _ _ NoFields) = []


createModule :: [Decl] -> Module 
createModule records = Module (Name (loc,"Hom")) NoParams (map createHom $ readRecords records)

start mod = map createHom $ readRecords mod
-- start mod = map rawPrintAfterParsing 
-- test ∷ FilePath → IO [Constr]]
test file =
  do s <- readFile file
     case (parseModule s) of
       Right (Module n p decls) ->
        do putStrLn "Generating Hom"
           return $ scopeCheckModule $ Module n p (decls ++ (map createHom $ readRecords decls)) 
 
  
     
{-
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
-}

