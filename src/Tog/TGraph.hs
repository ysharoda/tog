module Tog.TGraph where

import Tog.Raw.Abs
import Tog.Utils
import Tog.DerivingInsts()
  
import qualified Data.Generics      as Generics
import qualified Data.List          as List
import qualified Data.Map           as Map
import qualified Data.List.NonEmpty as NE
import           Data.List.Split
import           Data.Char(isSpace)
import           Tog.Parse(parseExpr) 


type Name_ = String
type Path  = NE.NonEmpty GView
type RenameFunc = Name_ -> Name_
type Mapping = Map.Map Name_ Name_

data GTheory = GTheory {
    params :: Params,
    fields :: Fields }
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data GView   = GView{
    source  :: GTheory,
    target  :: GTheory,
    mapping :: Mapping }  
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data QPath = QPath { -- Qualified path, i.e. a path with a rename
    path :: Path,
    mapp :: Mapping } deriving Show 

  
data TGraph = TGraph{ -- check if I would rather use only a map of edges
    nodes :: Map.Map Name_ GTheory,
    edges :: Map.Map Name_ GView } 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)


{- ------------------- Build the Graph  ----------------- -}
  
updateGraph ::  TGraph -> Name_ -> Either GView UTriangle -> TGraph
updateGraph graph newThryName (Left view) =
  TGraph (Map.insert newThryName (target view)  $ nodes graph)
         (Map.insert ("To"++newThryName) view $ edges graph)
-- TODO: find a way to get the name of the source theory. 
updateGraph graph newThryName (Right ut) =
   TGraph (Map.insert newThryName (target $ uLeft ut) $ nodes graph)
        $ (Map.fromList [("To"++newThryName++"1",uLeft ut),
                         ("To"++newThryName++"2",uRight ut),
                         ("To"++newThryName++"D",diagonal ut)])
          `Map.union` (edges graph)

{- ------------------- Elaborate Into TheoryGraph ---------------- -}

computeTransport :: Mapping -> GTheory -> GView
computeTransport rmap thry =
  GView thry (applyMapping thry rmap)
        (injectiveMapping rmap thry)   

-- --------- RENAME -----------
computeRename :: Mapping -> GTheory -> GView  
computeRename namesMap srcThry =
  GView srcThry (applyMapping srcThry namesMap)
       (injectiveMapping namesMap srcThry)

-- --------- EXTENSION ---------
computeExtend :: [Constr] -> GTheory -> GView
computeExtend newDecls srcThry =
  GView srcThry (extThry newDecls srcThry)
       (injectiveMapping Map.empty srcThry)
            
extThry :: [Constr] -> GTheory -> GTheory 
extThry newConstrs thry =
  if noNameConflict newConstrNames (symbols thry)
  then GTheory (params thry) $ newFields (fields thry) -- TODO: Decl added to param?
  else error $ "Cannot create theory "
  where newConstrNames = constrsNames newConstrs
        newFields NoFields = Fields newConstrs
        newFields (Fields fs) = Fields (fs ++ newConstrs)

-- ----------- COMBINE ----------- 
data UTriangle = UTriangle { -- upside triangle
   uLeft    :: GView,
   uRight   :: GView,
   diagonal :: GView} deriving Show 

getDest :: UTriangle -> GTheory
getDest utri =
  if (target (uLeft utri) == target (uRight utri)) && (target (uRight utri) == target (diagonal utri)) 
  then target $ uLeft utri
  else error "Views have different targets"

computeCombine :: TGraph -> QPath -> QPath -> UTriangle
computeCombine gr qpath1 qpath2 =
  let isTriangle = (pathSource $ path qpath1) == (pathSource $ path qpath2)
  --    src = pathSource $ path qpath1
  --    getView qp = GView src (pathTarget $ path qp) (composeMaps $ (NE.toList (NE.map mapping $ path qp)) ++ [mapp qp])
   in if (not isTriangle)
      then error "The two theories do not meet at the source"
      else if (not $ checkGuards gr qpath1 qpath2)
      then error "Name Clash!"         
      else createDiamond qpath1 qpath2 
   
upsideTriangle :: GView -> GView -> GView -> UTriangle
upsideTriangle v1 v2 diag =
  if (target v1 == target v2) && (target v2 == target diag) 
  then UTriangle v1 v2 diag 
  else error "Views have different targets"

-- Precondition: Called after checkGuards
createDiamond :: QPath -> QPath -> UTriangle
createDiamond left right =
 let commonSrc = qpathSource left
     lThry = applyCompositeMapping (qpathTarget left)  (path left)  (mapp left)
     rThry = applyCompositeMapping (qpathTarget right) (path right) (mapp right)
     srcMapped = applyCompositeMapping commonSrc (path left) (mapp left)
     newThry =
       GTheory (ParamDecl $ disjointUnion3 (getParams $ params srcMapped) (getParams $ params lThry) (getParams $ params rThry))
               (Fields    $ disjointUnion3 (getFields $ fields srcMapped) (getFields $ fields lThry) (getFields $ fields rThry))
     allMaps qp = composeMaps $ (map (\(GView _ _ m) -> m) $ NE.toList $ path qp) ++ [mapp qp]
     lView = GView (qpathTarget left)  newThry $ injectiveMapping (allMaps left) (qpathTarget left)
     rView = GView (qpathTarget right) newThry $ injectiveMapping (allMaps right) (qpathTarget right) 
     diag  = GView commonSrc newThry $ injectiveMapping (allMaps left) commonSrc   
  in upsideTriangle lView rView diag

{-
injectiveMapping :: Mapping -> GTheory -> Mapping

composeMaps :: [Mapping] -> Mapping
composeMaps mapsList =
  foldr composeTwoMaps Map.empty mapsList

mapAsFunc :: Mapping -> RenameFunc 
mapAsFunc m x =
  case Map.lookup x m of
    Nothing  -> x
    Just val -> val
-} 

getPath :: TGraph -> GTheory -> GTheory -> Path 
getPath graph src trgt =
  if src == trgt
  then error $ "source and target theories need to be different: source = " ++ getTheoryName graph src  ++ "; target = " ++ getTheoryName graph trgt
  else let p =  getPath' (Map.elems $ edges graph) src trgt
       in if p /= []
          then NE.fromList $ getPath' (Map.elems $ edges graph) src trgt 
          else error $ "path from " ++ getTheoryName graph src ++ " to " ++ getTheoryName graph trgt ++ " not found"

getPath' :: [GView] -> GTheory -> GTheory -> [GView] 
getPath' edgesList src dest =
  let answer = [v | v <- edgesList, target v == dest, source v == src]
      viewsToDest = [v | v <- edgesList, target v == dest]
      found = if answer /= [] then [[head answer]]
              else [(getPath' edgesList src (source v)) ++ [v] | v <- viewsToDest]
      p = List.filter (\ls -> pathSource (NE.fromList ls) == src) found             
   in if p == []
      then [] 
      else List.head p 

getTheoryName :: TGraph -> GTheory -> Name_
getTheoryName graph thry =
  let theories = Map.toList $ nodes graph
      targets = [k | (k,a) <- theories, a == thry]      
   in if length targets == 1
      then head targets
      else if length targets == 0
      then error $ "Theory Not found" ++ show theories 
      else error $ "Multiple theories with the same name : " ++ (show targets) 

getViewName :: TGraph -> GView -> Name_
getViewName graph view =
  let ed = Map.toList $ edges graph
      targets = [k | (k,a) <- ed, a == view]      
   in if length targets == 1
      then head targets
      else if length targets == 0
      then error "View Not found"
      else error "Multiple Views with the same name"           

           
                               
{- --------------------------------------------------------------- -}
liftMapping :: Mapping -> GTheory -> GView
liftMapping namesMap srcThry =
  GView srcThry (applyMapping srcThry namesMap)
        (injectiveMapping namesMap srcThry)
        

{- ------------------------ Utils --------------------------------- -}

lookupName :: Name_ -> TGraph -> GTheory
lookupName name graph =
  case (Map.lookup name $ nodes graph) of
    Nothing -> error $ name ++ "is not a valid theory name"
    Just t  -> t

qpathSource :: QPath -> GTheory
qpathSource qp = pathSource $ path qp

qpathTarget :: QPath -> GTheory
qpathTarget qp = pathTarget $ path qp 

pathSource :: Path -> GTheory
pathSource p = source $ NE.head p

pathTarget :: Path -> GTheory
pathTarget p = target $ NE.last p 

constrsNames :: [Constr] -> [Name_]
constrsNames constrs = map (\(Constr n _) -> nameToStr n) constrs 

applyMapping :: GTheory -> Mapping -> GTheory
applyMapping thry m =
  GTheory (Generics.everywhere (Generics.mkT $ mapAsFunc m) (params thry)) 
          (Generics.everywhere (Generics.mkT $ mapAsFunc m) (fields thry))

applyCompositeMapping :: GTheory -> Path -> Mapping -> GTheory
applyCompositeMapping thry pth mappings =
  applyMapping thry $
     composeMaps $ (map (\(GView _ _ m) -> m) $ NE.toList $ pth) ++ [mappings]
     
noNameConflict :: [Name_] -> [Name_] -> Bool
noNameConflict frst scnd = List.intersect frst scnd == []

-- allUnique snds --> no two symbols mapped to the same name
-- allUnique fsts --> no symbol mapped to two different names
-- noConflist --> The new names do not occur in the theory
validMapping :: Mapping -> GTheory -> Bool
validMapping namesMap thry =
  let syms = symbols thry 
      relevantMaps = [(k,a) | (k,a) <- Map.toList namesMap, (elem k syms), k/=a]
      noConflict = noNameConflict (map snd relevantMaps) (syms) 
      allUnique xs = List.nub xs == xs 
   in allUnique (map fst relevantMaps) && allUnique (map snd relevantMaps) && noConflict

-- turns a rename list into an injective mapping over the symbols of the source theory. 
injectiveMapping :: Mapping -> GTheory -> Mapping
injectiveMapping m srcThry =
  if validMapping m srcThry
  then Map.fromList $ List.map (\x -> (x, mapAsFunc m x)) $ symbols srcThry
  else error $ "cannot apply mapping " ++ (show (Map.toList m)) ++ " to theory with symbols " ++ show (symbols srcThry) 

disjointUnion3 :: Eq a => [a] -> [a] -> [a] ->  [a]
disjointUnion3 l1 l2 l3 = l1 ++ (l2 List.\\ l1) ++ (l3 List.\\ l1)


{- -------- Composing Maps ----------- -}

-- The list representation of Maps
composeTwoMaps :: Mapping -> Mapping -> Mapping
composeTwoMaps m1 m2 = Map.fromList $ composeTwoMaps' (Map.toList m1) m2 

composeTwoMaps' :: [(Name_ ,Name_)] -> Mapping -> [(Name_,Name_)]
composeTwoMaps' [] m = Map.toList m 
composeTwoMaps' ((x,y):ls) m =
  case  Map.lookup y m of
    Just val -> (x,val) : composeTwoMaps' ls (Map.delete y m)
    Nothing  -> (x,y)   : composeTwoMaps' ls m 

composeMaps :: [Mapping] -> Mapping
composeMaps mapsList =
  foldr composeTwoMaps Map.empty mapsList

mapAsFunc :: Mapping -> RenameFunc 
mapAsFunc m x =
  case Map.lookup x m of
    Nothing  -> x
    Just val -> val

{- ------------------------------------------------ -} 
    

symbols :: GTheory -> [Name_]
symbols thry =
  let 
    getArgs NoParams = []
    getArgs (ParamDef _) = [] 
    getArgs (ParamDecl bindsList) = Prelude.foldr (++) [] $ Prelude.map getBindingArgs bindsList 
    argNames   = Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) (getArgs $ params thry)    
    fieldNames = Generics.everything (++) (Generics.mkQ [] (\(Constr (Name (_,n)) _) -> [n])) thry
  in argNames ++ fieldNames     

checkGuards :: TGraph -> QPath -> QPath -> Bool
checkGuards gr qpath1 qpath2 =
  let sameSource = (pathSource $ path qpath1) == (pathSource $ path qpath2)
      -- mapsList views renMap = (mapAsFunc renMap)
      symsMapped qp = symbols $ applyCompositeMapping (pathSource $ path qp) (path qp) (mapp qp) 
      trgtSyms1 = symsMapped qpath1
      trgtSyms2 = symsMapped qpath2
   in if (sameSource &&
      trgtSyms1 == trgtSyms2) then True else error $ "Name Clash! between " ++ (show trgtSyms1)
                                             ++ " and " ++ (show trgtSyms2) ++ " when combining " ++ (getTheoryName gr $ qpathTarget qpath1) ++ " and " ++ (getTheoryName gr $ qpathTarget qpath2) 

noSrcLoc :: (Int,Int)
noSrcLoc = (0,0) 

parseConstr :: String -> Constr
parseConstr constr =
  let trim = List.dropWhileEnd isSpace . List.dropWhile isSpace
      namTyp = map trim $ splitOn ":" constr
      get_expr (Left _) = error "invalide declaration"
      get_expr (Right r) = r
  in  if length namTyp /= 2 then error "invalid declaration"
      else Constr (Name (noSrcLoc, head namTyp)) (get_expr $ parseExpr $ last namTyp) 
      

{-
type InputMap = [(Name_,Name_)]
type SConstr  = String 



data StrExpr = Rename Name_ InputMap 
             | Extend Name_ [SConstr]
             | Combine Name_ InputMap Name_ InputMap Name_

data ModExpr = RenameT Theory Mapping
               | ExtendT Theory [Constr]
               | CombineP QPath QPath deriving Show

def :: Name_ -> StrExpr -> TGraph -> TGraph
def name strExpr graph =
  case parse strExpr graph of
    RenameT srcThry renMap   -> updateGraph graph name $ Left  (computeRename renMap srcThry)
    ExtendT srcThry newDecls -> updateGraph graph name $ Left  (computeExtend newDecls srcThry)
    CombineP qpath1 qpath2   -> updateGraph graph name $ Right (computeCombine qpath1 qpath2) 

parse :: StrExpr -> TGraph -> ModExpr
parse (Rename name ren) graph = RenameT (lookupName name graph) (Map.fromList ren)
parse (Extend name decls) graph = ExtendT (lookupName name graph) (map parseConstr decls)
-- Combine "AdditiveMagma" [] "Pointed0" [] "Carrier"
parse (Combine name1 ren1 name2 ren2 nameSrc) graph =
  let srcThry = lookupName nameSrc graph
      path1 = getPath graph srcThry (lookupName name1 graph)
      path2 = getPath graph srcThry (lookupName name2 graph) 
  in CombineP (QPath path1 $ Map.fromList ren1) (QPath path2 $ Map.fromList ren2)
-}
