module Tog.TheoryGraph where

import Tog.Raw.Abs
import Tog.Utils
import Tog.DerivingInsts()
  
import qualified Data.Generics as Generics
import qualified Data.List     as List
import qualified Data.Map      as Map

data Theory = Theory {
    params :: Params,
    fields :: Fields }
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data View   = View{
    source  :: Theory,
    target  :: Theory,
    mapping :: Mapping }  
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data TGraph = TGraph{ -- check if I would rather use only a map of edges
    nodes :: Map.Map Name_ Theory,
    edges :: Map.Map Name_ View } 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

type Name_ = String
type Path  = [View]
type RenameFunc = Name_ -> Name_
type Mapping = Map.Map Name_ Name_ 

data ModExpr = Rename Theory Mapping
               | Extends Theory [Constr]
               | Combine Path Mapping Path Mapping
               -- not the export the constructor at the outside of the module 

updateGraph ::  TGraph -> Name_ -> Either View UTriangle -> TGraph
updateGraph graph newThryName (Left view) =
  TGraph (Map.insert newThryName (target view)  $ nodes graph)
         (Map.insert ("To"++newThryName) view $ edges graph)
-- TODO: find a way to get the name of the source theory. 
updateGraph graph newThryName (Right ut) =
  TGraph (Map.insert newThryName (target $ uLeft ut) $ nodes graph)
       $ (Map.fromList [("To"++newThryName++"1",uLeft ut),("To"++newThryName++"2",uRight ut)])
          `Map.union` (edges graph)

def :: Name_ -> ModExpr -> TGraph -> TGraph 
def name (Rename srcThry renMap) graph =
  updateGraph graph name $ Left  (computeRename renMap srcThry)
def name (Extends srcThry newDecls) graph =
  updateGraph graph name $ Left  (computeExtends newDecls srcThry)
def name (Combine p1 mapp1 p2 mapp2) graph =
  updateGraph graph name $ Right (computeCombine p1 mapp1 p2 mapp2) 


applyMapping :: Theory -> Mapping -> Theory 
applyMapping thry mapp =
  Theory (Generics.everywhere (Generics.mkT $ mapAsFunc mapp) (params thry)) 
         (Generics.everywhere (Generics.mkT $ mapAsFunc mapp) (fields thry)) 

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
injectiveMapping mapp srcThry =
  if validMapping mapp srcThry
  then Map.fromList $ zip (symbols srcThry) $ Prelude.map (mapAsFunc mapp) $ symbols srcThry
  else error "invalid Mapping"   

-- ------------------ Rename Combinator ---------------------------

computeRename :: Mapping -> Theory -> View  
computeRename namesMap srcThry =
  let targetThry = applyMapping srcThry namesMap
      renView = View srcThry targetThry $ injectiveMapping namesMap srcThry
  in renView        

-- --------------- Extends Combinator -----------------------------

extThry :: Theory -> [Constr] -> Theory
extThry thry newConstrs =
  if noNameConflict newDeclNames (symbols thry)
  then Theory (params thry) $ newFields (fields thry) -- TODO: Decl added to param? 
  else error $ "Cannot create theory "
  where newDeclNames = Prelude.map (\(Constr n _) -> nameToStr n) newConstrs
        newFields NoFields = Fields newConstrs
        newFields (Fields fs) = Fields (fs ++ newConstrs) 

computeExtends :: [Constr] -> Theory -> View  
computeExtends newDecls srcThry  =
  let targetThry = extThry srcThry newDecls
      extView = View srcThry targetThry $ injectiveMapping Map.empty srcThry
   in extView

-- --------------------- Combine ----------------------------------  

getViews :: TGraph -> Theory -> Theory -> Theory -> (Path,Path) 
getViews graph src dest1 dest2 =
  (path edgesList src dest1, path edgesList src dest2)
  where edgesList = (Map.elems $ edges graph)
        path :: [View] -> Theory -> Theory -> Path
        path edgs src_ dest =
           let answer = [v | v <- edgs, target v == dest, source v == src_]
               viewsToDest = [v | v <- edgs, target v == dest]
               found = if answer /= [] then [[head answer]]
                       else [(path edgs src_ (source v)) ++ [v] | v <- viewsToDest] 
           in Prelude.head $ Prelude.filter (\ls -> (source (head ls)) == src_) found
           -- change the head, check NEList 

checkGuards :: Path -> Path -> Bool
checkGuards path1 path2 =
  let nonEmptyPaths = path1 /= [] && path2 /= []
      sameSource = (source $ head path1) == (source $ head path2)
      srcSymbols = symbols $ source $ head path1
   in nonEmptyPaths && sameSource && 
      (List.map (mapSymbol path1) srcSymbols) == (List.map (mapSymbol path1) srcSymbols)

-- find the mapping of a symbol based on a list of views from the source to the destination theories.
-- used to check for the 
mapSymbol :: [View] -> RenameFunc 
mapSymbol lview sym =
  let getMappings = List.map (\v -> mapping v) lview
   in mapAsFunc (composeMaps getMappings) sym
      -- findMatch getMappings sym -- Prelude.foldr (.) strId $ List.map pairToFunc getMappings

-- The overall view resulting from the path. 
{-
composeViews :: [View] -> Mapping
composeViews vlist =
  let sourceSyms = symbols $ source (head vlist)
   in zip sourceSyms $ List.map (mapSymbol vlist) sourceSyms 
-}
disjointUnion3 :: Eq a => [a] -> [a] -> [a] ->  [a]
disjointUnion3 l1 l2 l3 = l1 ++ (l2 List.\\ l1) ++ (l3 List.\\ l1) 


data Triangle = Triangle {
  left  :: View,
  right :: View }

data UTriangle = UTriangle {
   uLeft  :: View,
   uRight :: View } 

triangle :: View -> View -> Triangle
triangle v1 v2 =
  if (source v1 == source v2)
  then Triangle v1 v2
  else error "Views have different sources"

upsideTriangle :: View -> View -> UTriangle
upsideTriangle v1 v2 =
  if (target v1 == target v2)
  then UTriangle v1 v2
  else error "Views have different targets" 

-- Precondition:
--  - Called after checkGuards
createDiamond :: Triangle -> UTriangle
createDiamond t =
  let commonSrc = source $ left t
      lThry = target $ left t
      rThry = target $ right t 
--      (lThry,rThry) = fmap target (left t,right t) 
      newThry =
        Theory (ParamDecl $ disjointUnion3 (getParams $ params commonSrc) (getParams $ params lThry) (getParams $ params $ rThry))
               (Fields    $ disjointUnion3 (getFields $ fields commonSrc) (getFields $ fields rThry) (getFields $ fields rThry))
      lView = View lThry newThry (mapping $ right t)
      rView = View rThry newThry (mapping $ left  t) 
  in upsideTriangle lView rView                        

-- this function is called after guard is checked
computeCombine :: Path -> Mapping -> Path -> Mapping -> UTriangle
computeCombine path1 ren1 path2 ren2 =
  let cView1 = View (source $ head $ path1) (target $ last $ path2) (composeMaps $ (List.map mapping path1) ++ [ren1])
      cView2 = View (source $ head $ path2) (target $ last $ path2) (composeMaps $ (List.map mapping path2) ++ [ren2])
  in createDiamond $ triangle cView1 cView2

-- EDNOTE: find a better way to arrange these arguments
{-
combine :: TGraph -> Name_ -> Name_ -> Name_ -> Mapping -> Name_ -> Mapping -> (Theory,View,View)
combine graph newThryName srcName d1Name ren1 d2Name ren2 =
    let [src,dest1,dest2] = map (getTheoryFromName $ nodes graph) [srcName,d1Name,d2Name] 
        (path1,path2) = getViews graph src dest1 dest2
    in if checkGuard path1 path2
               then computeCombine newThryName path1 ren1 path2 ren2
               else error "Cannot compute the expr" 
     -}
-- ----------------------------------------------------------------

-- ------------------------ Helper Functions -------------------------

mapAsFunc :: Mapping -> RenameFunc 
mapAsFunc mapp x =
  case Map.lookup x mapp of
    Nothing  -> x
    Just val -> val

composeMapsToFunc :: [Mapping] -> RenameFunc 
composeMapsToFunc mapsList =
  foldr (.) id $ List.map mapAsFunc $ List.reverse mapsList

composeMaps :: [Mapping] -> Mapping
composeMaps ls =
  funcToMapping (composeMapsToFunc ls) (Map.keys $ head ls) 

funcToMapping :: RenameFunc -> [Name_] -> Mapping   
funcToMapping f syms =
  Map.fromList $ zip syms (map f syms)
{-
composeMaps :: Mapping -> Mapping -> Mapping
composeMaps m1 m2 =
  let symbols = keys m1
  -}    
{-
pairToFunc :: Mapping -> RenameFunc 
pairToFunc list name = if result == [] then name
                       else if (length result) == 1 then head result
                       else error "Multiple mappings for the same symbol" 
  where result = Prelude.map snd $ Prelude.filter (\x -> fst x ==  name) list 
-}
-- the symbols of a theory 
symbols :: Theory -> [Name_]
symbols thry =
  let 
    getArgs NoParams = []
    getArgs (ParamDef _) = [] 
    getArgs (ParamDecl bindsList) = Prelude.foldr (++) [] $ Prelude.map getBindingArgs bindsList 
    argNames   = Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) (getArgs $ params thry)    
    fieldNames = Generics.everything (++) (Generics.mkQ [] (\(Constr (Name (_,n)) _) -> [n])) thry
  in argNames ++ fieldNames     


{- --------------------- tests ------------------------- -}
{-
empty = Theory NoParams NoFields

test =
  def "magma" (Extends pointed createBinFunc "op" "A")
    $ def "pointed" (Extends carrier createConst "e" "A")
    $ def "carrier" (Extends empty createConst "A" "Set") 
-}
{- -------------- Helper ---------------- -}
noSrcLoc :: (Int,Int)
noSrcLoc = (0,0) 

createNQArg :: Name_ -> Arg 
createNQArg str = Arg $ Id $ NotQual $ Name (noSrcLoc,str) 

createConst :: Name_ -> Name_ -> Constr 
createConst name typeName =
  Constr (Name (noSrcLoc,name)) (App [createNQArg typeName])

createBinFunc :: Name_ -> Name_ -> Constr
createBinFunc name typeName = 
  Constr (Name (noSrcLoc,name))
    (Fun (App [createNQArg typeName])
         $ Fun (App [createNQArg typeName]) (App [createNQArg typeName]))
