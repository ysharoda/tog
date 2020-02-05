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
type Path  = NE.NonEmpty View
type RenameFunc = Name_ -> Name_
type Mapping = Map.Map Name_ Name_

data Theory = Theory {
    params :: Params,
    fields :: Fields }
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data View   = View{
    source  :: Theory,
    target  :: Theory,
    mapping :: Mapping }  
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data QPath = QPath { -- Qualified path, i.e. a path with a rename
    path :: Path,
    mapp :: Mapping } deriving Show 

data TGraph = TGraph{ -- check if I would rather use only a map of edges
    nodes :: Map.Map Name_ Theory,
    edges :: Map.Map Name_ View } 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)


data ModExpr = RenameT Theory Mapping
               | ExtendT Theory [Constr]
               | CombineP QPath QPath deriving Show 

{- ------------------- Read The Input  ----------------- -}

type InputMap = [(Name_,Name_)]
type SConstr  = String 

data StrExpr = Rename Name_ InputMap 
             | Extend Name_ [SConstr]
             | Combine Name_ InputMap Name_ InputMap Name_

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

  
updateGraph ::  TGraph -> Name_ -> Either View UTriangle -> TGraph
updateGraph graph newThryName (Left view) =
  TGraph (Map.insert newThryName (target view)  $ nodes graph)
         (Map.insert ("To"++newThryName) view $ edges graph)
-- TODO: find a way to get the name of the source theory. 
updateGraph graph newThryName (Right ut) =
  TGraph (Map.insert newThryName (target $ uLeft ut) $ nodes graph)
       $ (Map.fromList [("To"++newThryName++"1",uLeft ut),("To"++newThryName++"2",uRight ut)])
          `Map.union` (edges graph)

{- ------------------- Elaborate Into TheoryGraph ---------------- -}

-- --------- RENAME -----------
computeRename :: Mapping -> Theory -> View  
computeRename namesMap srcThry =
  View srcThry (applyMapping srcThry namesMap)
       (injectiveMapping namesMap srcThry)

-- --------- EXTENSION ---------
computeExtend :: [Constr] -> Theory -> View
computeExtend newDecls srcThry =
  View srcThry (extThry newDecls srcThry)
       (injectiveMapping Map.empty srcThry)
            
extThry :: [Constr] -> Theory -> Theory 
extThry newConstrs thry =
  if noNameConflict newConstrNames (symbols thry)
  then Theory (params thry) $ newFields (fields thry) -- TODO: Decl added to param?
  else error $ "Cannot create theory "
  where newConstrNames = constrsNames newConstrs
        newFields NoFields = Fields newConstrs
        newFields (Fields fs) = Fields (fs ++ newConstrs)

-- ----------- COMBINE ----------- 
data UTriangle = UTriangle { -- upside triangle
   uLeft  :: View,
   uRight :: View }               

computeCombine :: QPath -> QPath -> UTriangle
computeCombine qpath1 qpath2 =
  let isTriangle = (pathSource $ path qpath1) == (pathSource $ path qpath2)
      src = pathSource $ path qpath1
      getView qp = View src (pathTarget $ path qp) (composeMaps $ (NE.toList (NE.map mapping $ path qp)) ++ [mapp qp])
   in if (not isTriangle) || (not $ checkGuards (path qpath1) (path qpath2)) 
      then error "The two theories do not meet at the source"
      else createDiamond (getView qpath1) (getView qpath2) 
   
upsideTriangle :: View -> View -> UTriangle
upsideTriangle v1 v2 =
  if (target v1 == target v2)
  then UTriangle v1 v2
  else error "Views have different targets"

-- Precondition: Called after checkGuards
createDiamond :: View -> View -> UTriangle
createDiamond left right =
 let commonSrc = source $ left
     lThry = target left
     rThry = target right
     srcMapped = applyMapping commonSrc (mapping left)
     newThry =
        Theory (ParamDecl $ disjointUnion3 (getParams $ params srcMapped) (getParams $ params lThry) (getParams $ params rThry))
               (Fields    $ disjointUnion3 (getFields $ fields srcMapped) (getFields $ fields lThry) (getFields $ fields rThry))
     lView = View lThry newThry (mapping $ right)
     rView = View rThry newThry (mapping $ left) 
  in upsideTriangle lView rView

getPath :: TGraph -> Theory -> Theory -> Path
getPath graph src trgt =
  if src == trgt
  then error "source and target theories need to be different"
  else NE.fromList $ (getPath' (Map.elems $ edges graph) src trgt)

getPath' :: [View] -> Theory -> Theory -> [View]
getPath' edgesList src dest =
  let answer = [v | v <- edgesList, target v == dest, source v == src]
      viewsToDest = [v | v <- edgesList, target v == dest]
      found = if answer /= [] then [[head answer]]
              else [(getPath' edgesList src (source v)) ++ [v] | v <- viewsToDest]
      p = List.filter (\ls -> pathSource (NE.fromList ls) == src) found             
   in if p == []
      then error "path not found"
      else List.head p 
  
  

{- ------------------------ Utils --------------------------------- -}

lookupName :: Name_ -> TGraph -> Theory
lookupName name graph =
  case (Map.lookup name $ nodes graph) of
    Nothing -> error $ name ++ "is not a valid theory name"
    Just t  -> t

pathSource :: Path -> Theory
pathSource p = source $ NE.head p

pathTarget :: Path -> Theory
pathTarget p = target $ NE.last p 

constrsNames :: [Constr] -> [Name_]
constrsNames constrs = map (\(Constr n _) -> nameToStr n) constrs 

applyMapping :: Theory -> Mapping -> Theory
applyMapping thry m =
  Theory (Generics.everywhere (Generics.mkT $ mapAsFunc m) (params thry)) 
         (Generics.everywhere (Generics.mkT $ mapAsFunc m) (fields thry)) 

noNameConflict :: [Name_] -> [Name_] -> Bool
noNameConflict frst scnd = List.intersect frst scnd == []

-- allUnique snds --> no two symbols mapped to the same name
-- allUnique fsts --> no symbol mapped to two different names
-- noConflist --> The new names do not occur in the theory
validMapping :: Mapping -> Theory -> Bool
validMapping namesMap thry =
  let fsts = Map.keys namesMap 
      snds = Map.elems namesMap      
      nonIdMaps  = Map.filterWithKey (\k a -> k /= a) namesMap
      noConflict = noNameConflict (Map.elems nonIdMaps) (symbols thry) 
      allUnique xs = List.nub xs == xs 
   in allUnique snds && allUnique fsts && noConflict

-- turns a rename list into an injective mapping over the symbols of the source theory. 
injectiveMapping :: Mapping -> Theory -> Mapping
injectiveMapping m srcThry =
  if validMapping m srcThry
  then Map.fromList $ List.map (\x -> (x, mapAsFunc m x)) $ symbols srcThry
  else error "invalid Mapping"

disjointUnion3 :: Eq a => [a] -> [a] -> [a] ->  [a]
disjointUnion3 l1 l2 l3 = l1 ++ (l2 List.\\ l1) ++ (l3 List.\\ l1)

composeMapsToFunc :: [Mapping] -> RenameFunc 
composeMapsToFunc mapsList =
  foldr (.) id $ List.map mapAsFunc $ List.reverse mapsList

composeViewsToFunc :: [View] -> RenameFunc
composeViewsToFunc viewsList =
  composeMapsToFunc (List.map mapping viewsList) 

composeMaps :: [Mapping] -> Mapping
composeMaps ls =
  funcToMapping (composeMapsToFunc ls) (Map.keys $ head ls) 

funcToMapping :: RenameFunc -> [Name_] -> Mapping   
funcToMapping f syms =
  Map.fromList $ zip syms (map f syms)

mapAsFunc :: Mapping -> RenameFunc 
mapAsFunc m x =
  case Map.lookup x m of
    Nothing  -> x
    Just val -> val

symbols :: Theory -> [Name_]
symbols thry =
  let 
    getArgs NoParams = []
    getArgs (ParamDef _) = [] 
    getArgs (ParamDecl bindsList) = Prelude.foldr (++) [] $ Prelude.map getBindingArgs bindsList 
    argNames   = Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) (getArgs $ params thry)    
    fieldNames = Generics.everything (++) (Generics.mkQ [] (\(Constr (Name (_,n)) _) -> [n])) thry
  in argNames ++ fieldNames     

checkGuards :: Path -> Path -> Bool
checkGuards path1 path2 =
  let sameSource = (pathSource path1) == (pathSource path2)
      srcSymbols = symbols $ pathSource path1
   in sameSource && 
      (List.map (composeViewsToFunc (NE.toList path1)) srcSymbols) == (List.map (composeViewsToFunc (NE.toList path2)) srcSymbols)

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
      
