module Tog.Hom where

{-
 - Generating Homomorphism definitions for single-sorted 
 -} 

import Tog.Raw.Abs
import Tog.Utils
import Tog.DerivingInsts()
import Data.List as List 

import qualified Data.Generics as Generics

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

{- Generating the hidden arguments
  --> generated from the original argument of the record -} 

oneBindAsHiddenArg :: Binding -> [Binding]
oneBindAsHiddenArg bind =
  let justArgNames = map getArgName $ getBindingArgs bind
      argNames = map (maybe "" (++"")) justArgNames
      oldNewPairs str = zip argNames $ map (++str) argNames
      newBinding [] b = b 
      newBinding ((old,new):xs) b = newBinding xs (renameBinding old new b)
      inst1Bind = newBinding (oldNewPairs "1") bind
      inst2Bind = newBinding (oldNewPairs "2") bind
   in mergeBindings Hide inst1Bind inst2Bind
      
homHiddenArgs :: [Binding] -> [Binding] 
homHiddenArgs bindsList = concat $ map oneBindAsHiddenArg bindsList 

getParamNames :: String -> [Binding] -> [String] 
getParamNames str bindsList =
  let maybeNames = map getArgName $ concat $ map getBindingArgs bindsList
   in map (maybe "" (++str)) maybeNames
{-
 Generating the record instances 
-}

{- ------------- new code -------------- -} 
data Record = TRecord Name Params RecordBody 

createMapping ::  [Name_] -> Int -> [Name_]
createMapping name index = map (\n -> n++index) names

createInsts :: Record -> Index -> Record
createInsts (TRecord n p body) index =
  let ren = \n -> if n == "Set" then "Set" else n++index
  in TRecord (head n ++ index)
             (Generics.everywhere (Generics.mkT $ ren) p) 
             (Generics.everywhere (Generics.mkT $ ren) body)


{- ----------- end new code ------------- -}

             
createInstance :: Name -> String -> [Binding] -> Binding
createInstance n str binds =
  let recordName = nameStr n
      createName = strToArg $ instanceName ++ str
      instArgs = map strToArg $ getParamNames str binds
      createType = App ([strToArg $ recordName]++instArgs)
   in Bind [createName] createType

{- Generating the parameter to the homomorphism record -}
createHomParams :: Name -> Params -> Params
createHomParams _ NoParams = NoParams
createHomParams _ (ParamDef _) = NoParams
createHomParams name (ParamDecl bindslist)
   = ParamDecl $ homHiddenArgs bindslist
               ++ [createInstance name suffix1 bindslist]
               ++ [createInstance name suffix2 bindslist] 

createHomFunc :: Constr -> Constr
createHomFunc (Constr (Name (_,n)) _) =
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

genVars :: Int -> [String] 
genVars i = zipWith (++) (take i $ repeat "x") $ map show [1..i]

genBind :: Expr -> [Binding]
genBind expr =
  let args  = map (\x -> Arg $ createIdNQ x) $ genVars $ arity expr
      rename (Arg (Id (NotQual (Name (l,n))))) =
             (Arg (Id (NotQual (Name (l,n++suffix1)))))
      rename harg = error $ "Unexpected Pattern" ++ show harg 
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
       x -> error $ "Invalid expr " ++ show x

genLHS :: Constr -> Name -> Expr
genLHS constr inst = genHomFuncApp constr inst

genRHS :: Constr -> Name -> Expr
genRHS (Constr name expr) inst =
  let funcName = App [strToArg (nameToStr name), strToArg (nameToStr inst)]
      vars  = map (\x -> createIdNQ x) $ genVars $ arity expr
      args (Id qname) = genHomFuncApp (Constr (Name ((6,6),"dummy")) (Id qname)) inst
      args x =  error $ "Invalid expr " ++ show x
--      args (App [Arg a]) = args a
--      args (App (a:as)) = args (App [a]) ++ (args $ App as)
--      args (Fun e1 e2)  = args e1 ++ args e2  
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

createHom :: Record -> Decl
createHom (TRecord name params body) =
  Record (homRecordName name) 
         (createHomParams name params)
         (RecordDeclDef (Name (loc,"Set"))
                        (Name (loc,nameToStr name ++ "hom"))
                        (Fields $ createHomBody $ (getConstr body) ++ (paramsToFields params)))
       where getConstr (RecordDecl _) = []
             getConstr (RecordDef _ NoFields) = []
             getConstr (RecordDef _ (Fields c)) = c
             getConstr (RecordDeclDef _ _ NoFields) = []
             getConstr (RecordDeclDef _ _ (Fields c)) = c 



appendToModule :: Module -> [Decl] -> Module
appendToModule (Module n p (Decl_ decls)) moreDecls = Module n p $ Decl_ (decls ++ moreDecls)
appendToModule _ _ = error $ "Theory expressions are not properly flattened" 

-- TODO: find a better way 
-- The case of Module_ in Decl 
type InnerModule = Decl 

appendToModule_ :: InnerModule -> [Decl] -> InnerModule
appendToModule_ (Module_ (Module n p (Decl_ decls))) newDecls =
  Module_ $ Module n p (Decl_ $ decls ++ newDecls) 

paramsToFields :: Params -> [Constr]
paramsToFields NoParams       = []
paramsToFields (ParamDef  _)  = []
paramsToFields (ParamDecl bs) =
  concat $ map flattenBind bs
  where getNameQ :: QName -> Name
        getNameQ (Qual _ n)  = n
        getNameQ (NotQual n) = n 
        flattenBind :: Binding -> [Constr] 
        flattenBind bind =
           let flattenArg (Arg  (Id q)) = getNameQ q
               flattenArg (HArg (Id q)) = getNameQ q
               flattenArg x = error $ "invalid argument" ++ show x 
               names = map flattenArg $ getBindingArgs bind
           in  map (\(n,t) -> Constr n t) $ zip names (take (length $ getBindingArgs bind) (repeat $ getBindingExpr bind))

{- Testing -} 
-- Given all declarations in the file, we filter the records
emptyModule :: Module
emptyModule = Module (Name ((0,0),"Empty")) NoParams $ Decl_ []



readModuleRecords :: Module -> [Record]
readModuleRecords (Module _ _ (Decl_ decls)) =
  List.concatMap declRecords decls

readInnerModuleRecords :: InnerModule -> [Record]   
readInnerModuleRecords (Module_ mod) =
  readModuleRecords mod
readInnerModuleRecords _ = error "not a module"  

processModule :: Module -> Module 
processModule (Module n p (Decl_ decls)) =
  Module n p (Decl_ $ map processModule_ decls)

processModule_ mod =
  appendToModule_ mod (map createHom $ readInnerModuleRecords mod) 

declRecords :: Decl -> [Record]
declRecords decl = 
  Generics.everything (++) (Generics.mkQ [] (\(Record n p body) -> [TRecord n p body])) decl

--testSyb :: Module -> [Record]
testSyb decl = 
  Generics.everything (++) (Generics.mkQ [] (\(Id n) -> [n])) decl


-- needed for testing 
recordToDecl :: [Record] -> [Decl]
recordToDecl rls = map (\(LRecord n p r) -> (Record n p r)) rls 

flattenRecordBody :: RecordBody -> [Constr]
flattenRecordBody (RecordDecl _) = []
flattenRecordBody (RecordDef _ NoFields) = [] 
flattenRecordBody (RecordDef _ (Fields l)) = l
flattenRecordBody (RecordDeclDef _ _ (Fields l)) = l
flattenRecordBody (RecordDeclDef _ _ NoFields) = []


-- instantiate an argument

{-

[Tog.Raw.Bind [Tog.Raw.Arg (Tog.Raw.Id (Tog.Raw.NotQual (Tog.Raw.Name ((0,0),"A"))))] (Tog.Raw.App [Tog.Raw.Arg (Tog.Raw.Id (Tog.Raw.NotQual (Tog.Raw.Name ((0,0),"Set"))))]),
Tog.Raw.Bind [Tog.Raw.Arg (Tog.Raw.Id (Tog.Raw.NotQual (Tog.Raw.Name ((0,0),"e"))))] (Tog.Raw.App [Tog.Raw.Arg (Tog.Raw.Id (Tog.Raw.NotQual (Tog.Raw.Name ((0,0),"A"))))])]

-}
{- 
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
instanceArgs :: String -> [Binding] -> [Arg]
instanceArgs []     _   = [] 
instanceArgs str (b:bs) =
  map (instantiateArg str) $ arguments b
   ++ instanceArgs str bs
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
  where inst = instanceArgs index bindings

createHomParam :: Name -> Params -> Params
createHomParam n NoParams     = NoParams
createHomParam n (ParamDef _) = NoParams -- ??
createHomParam n (ParamDecl bindings) =
  ParamDecl $ (map createHiddenBindings bindings)
              ++ [instantiateRecord n bindings suffix1]
              ++ [instantiateRecord n bindings suffix2]
-}
{- create the Hom declarations -}  
     
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

