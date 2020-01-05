module Hom where

import Tog.Raw.Abs
import Tog.Parse
import Tog.ScopeCheck 
import Data.Functor


{-
Generating the homomorphism of single sorted theories of type Set.
- first, we classify the theory into sort, function symbols and axioms.
- At this point, we know there is one sort in the theories 
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
    Id (NotQual (Name (_,"Set"))) -> False
    Id (NotQual (Name (_,_)))     -> True
    Id (Qual _  (Name (_,"Set"))) -> False
    Id (Qual _  (Name (_,_)))     -> True
    App args@((Arg  _):_)   -> and $ map (\(Arg a)  -> isFunc a) args
    App args@((HArg  _):_)  -> and $ map (\(HArg a) -> isFunc a) args
    Fun e1 e2 -> isFunc e1 && isFunc e2
    Pi  _ e   -> isFunc e
    _         -> False

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

{- QQ: Is there a predefined function that does that. Functor does not work here -} 
liftFilter :: (Expr -> Bool) -> [Constr] -> [Constr]
liftFilter _ [] = [] 
liftFilter p ((Constr n e):xs) =
  if p e then (Constr n e) : liftFilter p xs
         else  liftFilter p xs 

classify :: [Constr] -> ([Constr],[Constr],[Constr])
classify ls = (liftFilter isSort ls,
               liftFilter isFunc ls,
               liftFilter isAxiom ls)

-- Dummy location for now
loc :: (Int,Int)
loc = (0,0)

nameToStr :: Name -> String
nameToStr (Name (_,n)) = n 

qnameToStr :: QName -> String
qnameToStr (NotQual name) = nameToStr name 
qnameToStr (Qual q  name) = qnameToStr q ++ "." ++ nameToStr name

argName :: Arg -> Maybe String
argName (Arg e) = -- TODO: The HArg case 
  case e of
    Id  qname     -> Just $ qnameToStr qname 
    App [Arg  e'] -> argName (Arg  e')
    App [HArg e'] -> argName (HArg e') 
    _             -> Nothing

data RecComponents =
    PConstr Constr
  | FConstr Constr 

homRecordName :: Name -> Name
homRecordName (Name (_,n)) = Name ((1,1),n++"Hom") 


{- Creating the Parameters to the Hom record -} 
suffix1 :: String
suffix1 = "1"
suffix2 :: String 
suffix2 = "2"

createNotQualId :: String -> Expr
createNotQualId str = Id (NotQual (Name ((2,2),str)))

instanceBinding :: [Binding] -> String -> [Arg]
instanceBinding []     _   = [] 
instanceBinding (b:bs) str =
  case b of
    Bind  args exp -> (map instanceArg args) ++ instanceBinding bs str
    HBind args exp -> (map instanceArg args) ++ instanceBinding bs str
  where
    instanceArg (HArg e) = instanceArg (Arg e) 
    instanceArg (Arg e)  = 
     case e of
       Id  qname     -> Arg (createNotQualId ((qnameToStr qname) ++ str))                   
       App [Arg  e'] -> instanceArg (Arg  e') 
       App [HArg e'] -> instanceArg (Arg e')
       _             -> error "Argument without name"

duplicateArg :: Arg -> [Arg]
duplicateArg arg =
  case arg of
    Arg  e -> duplicateArg' e  
    HArg e -> duplicateArg' e  
  where
   duplicateArg' e = 
     case e of
       Id  qname     -> [Arg (createNotQualId (qn ++ suffix1)),
                         Arg (createNotQualId (qn ++ suffix2))]
                        where qn = qnameToStr qname
       App [Arg  e'] -> duplicateArg (Arg  e') 
       App [HArg e'] -> duplicateArg (HArg e')
       _             -> error "Argument without name"
 

createBinding :: Binding -> Binding
createBinding binding =
  case binding of
    HBind args e -> HBind (newargs args) e
    Bind  args e -> HBind (newargs args) e
  where newargs args_list = concat $ map duplicateArg args_list 

instanceName :: String
instanceName = "inst"
createInstances :: Name -> [Binding]-> String -> Binding
createInstances (Name (_,n)) bindings index =
  Bind [Arg (Id (NotQual (Name ((3,3),instanceName++index))))]
       (App ([Arg $ Id $ NotQual $ (Name ((4,4),n))] ++ inst))
  where inst = instanceBinding bindings index

createHomParam :: Name -> Params -> Params
createHomParam n NoParams     = NoParams
createHomParam n (ParamDef _) = NoParams -- ??
createHomParam n (ParamDecl bindings) =
  ParamDecl $ (map createBinding bindings)
              ++ [createInstances n bindings suffix1]
              ++ [createInstances n bindings suffix2]

{- create the Hom declarations -}

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

homFuncName :: String 
homFuncName = "hom"
createHomFunc :: Constr -> Constr
createHomFunc c@(Constr (Name (_,n)) e) =
  Constr (Name ((5,5),homFuncName))
         (Fun (name suffix1)
              (name suffix2))
   where name str = App [Arg (createNotQualId (n ++ str))]

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
  let args  = map (\x -> Arg $ createNotQualId x) $ genVars $ arity expr
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
      vars  = map (\x -> createNotQualId x) $ genVars $ arity expr
   in case expr of
       Id qname -> [Arg $ Id qname] 
       App _    -> map Arg $ funcName:vars
       Fun _ _  -> [Arg $ App $ map Arg $ funcName:vars] 

genLHS :: Constr -> Name -> Expr
genLHS constr inst = genHomFuncApp constr inst

genRHS :: Constr -> Name -> Expr
genRHS (Constr name expr) inst =
  let funcName = App [strToArg (nameToStr name), strToArg (nameToStr inst)]
      vars  = map (\x -> createNotQualId x) $ genVars $ arity expr
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
  

nameStr :: Name -> String 
nameStr (Name (_,n)) = n 

strToArg :: String -> Arg 
strToArg str = Arg $ createNotQualId str



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
         return $ res
         where Right res =
                 scopeCheckModule $ Module n p (decls ++ (map createHom $ readRecords decls)) 
 
  
     
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
