module TheoryGraph where

import Tog.Raw.Abs
import Tog.Utils
import Tog.DerivingInsts
  
import qualified Data.Generics as Generics
import qualified Data.List     as List
import qualified Data.Map      as Map
import Control.Monad.State

data Theory = Theory {
    params :: Params,
    fields :: Fields }
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)
 
data View   = View{
    source  :: Theory,
    target  :: Theory,
    mapping :: Mapping } -- change this mapping too 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data TGraph = TGraph{ -- check is I would rather use only a map of edges
    nodes :: Map.Map Name_ Theory,
    edges :: Map.Map Name_ View } 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

type Name_ = String
type Path  = [View]
type RenameFunc = Name_ -> Name_
type Mapping = [(Name_,Name_)] -- Mapping (Map.Map Name_ Name_) 

data ModExpr = Rename Theory Mapping
               | Extends Theory [Constr]
               | Combine Path Mapping Path Mapping
               -- not the export the constructor at the outside of the module 

-- newtype State s a = State { runState :: s -> (a,s) }
{-
def :: Name_ -> ModExpr -> State TGraph Theory
def name (Rename srcThry renMap) =
  let (newT,newV) = rename renMap srcThry
      viewName = "To" ++ name -- TODO: Better view name 
      updateGraph =
        (\(TGraph thrys views) -> (newT,TGraph (Map.insert name newT thrys) (Map.insert viewName newV views))) 
  in  State (\oldGraph -> (newT,updateGraph oldGraph))
-}


{-
def name (Extends srcThry newDecls) =
  let (newT,newV) = extends newDecls srcThry
      updateGraph = (\oldGraph -> addThryToGraph newT $ addViewToGraph newV oldGraph)  
  in  StateT (newT,\oldGraph -> updateGraph)  
-}
{-
def name (Combine view1 renMap1 view2 renMap2) =
  let (newT,v1,v2) = computeCombine newThryName view1 renMap1 view2 renMap2
  in  newT 
-}




applyMapping :: Theory -> Mapping -> Theory 
applyMapping thry mapp =
  Theory (Generics.everywhere (Generics.mkT $ pairToFunc mapp) (params thry)) 
         (Generics.everywhere (Generics.mkT $ pairToFunc mapp) (fields thry)) 

noNameConflict :: [Name_] -> [Name_] -> Bool
noNameConflict frst scnd = List.intersect frst scnd == []
  
-- allUnique snds --> no two symbols mapped to the same name
-- allUnique fsts --> no symbol mapped to two different names
-- noConflist --> The new names do not occur in the theory
validMapping :: Mapping -> Theory -> Bool
validMapping namesMap thry =
  let fsts = Prelude.map fst namesMap 
      snds = Prelude.map snd namesMap      
      nonIdMaps  = Prelude.filter (\(x,y) -> x /= y) namesMap
      noConflict = noNameConflict (Prelude.map snd nonIdMaps) (symbols thry) 
      allUnique xs = List.nub xs == xs 
   in allUnique snds && allUnique fsts && noConflict
      

-- turns a rename list into an injective mapping over the symbols of the source theory. 
injectiveMapping :: Mapping -> Theory -> Mapping
injectiveMapping mapp srcThry =
  if validMapping mapp srcThry
  then zip (symbols srcThry) $ Prelude.map (pairToFunc mapp) $ symbols srcThry
  else error "invalid Mapping"   

-- ------------------ Rename Combinator ---------------------------

rename :: Mapping -> Theory -> (Theory,View)  
rename namesMap srcThry =
  let targetThry = applyMapping srcThry namesMap
      renView = View srcThry targetThry
                     (injectiveMapping namesMap srcThry)
  in (targetThry,renView)        

-- -------------- Extends Combinator -----------------------------

extThry :: Theory -> [Constr] -> Theory
extThry thry newConstrs =
  if noNameConflict newDeclNames (symbols thry)
  then Theory (params thry) $ newFields (fields thry) -- TODO: Decl added to param? 
  else error $ "Cannot create theory "
  where newDeclNames = Prelude.map (\(Constr n _) -> nameToStr n) newConstrs
        newFields NoFields = Fields newConstrs
        newFields (Fields fs) = Fields (fs ++ newConstrs) 

extends :: [Constr] -> Theory -> (Theory,View)  
extends newDecls srcThry  =
  let targetThry = extThry srcThry newDecls
      extView = View srcThry
                     targetThry
                     (injectiveMapping [] srcThry)
   in (targetThry,extView) 

-- --------------------- Combine ----------------------------------  

getViews :: TGraph -> Theory -> Theory -> Theory -> (Path,Path) 
getViews graph src dest1 dest2 =
  (path edgesList src dest1, path edgesList src dest2)
  where edgesList = (Map.elems $ edges graph)
        path :: [View] -> Theory -> Theory -> Path
        path edgs src dest =
           let answer = [v | v <- edgs, target v == dest, source v == src]
               viewsToDest = [v | v <- edgs, target v == dest]
               found = if answer /= [] then [[head answer]]
                       else [(path edgs src (source v)) ++ [v] | v <- viewsToDest] 
           in Prelude.head $ Prelude.filter (\ls -> (source (head ls)) == src) found
           -- change the head, check NEList 

checkGuard :: Path -> Path -> Bool
checkGuard path1 path2 =
  let nonEmptyPaths = path1 /= [] && path2 /= [] 
      srcThry = if (source (head path1)) == (source (head path2)) then source (head path1) else error "invalid arrows"
      srcSyms = symbols srcThry
   in nonEmptyPaths &&
      (List.map (mapSymbol path1) srcSyms) == (List.map (mapSymbol path1) srcSyms)

-- find the mapping of a symbol based on a list of views from the source to the destination theories.
-- used to check for the 
mapSymbol :: [View] -> RenameFunc 
mapSymbol lview sym =
  let getMappings = List.concat $ List.map (\v -> mapping v) lview
      findMatch [] x = x
      findMatch ((f,s):fs) x =
          if (x == f) then findMatch fs s else findMatch fs x 
   in findMatch getMappings sym -- Prelude.foldr (.) strId $ List.map pairToFunc getMappings

-- The overall view resulting from the path. 
composeViews :: [View] -> Mapping
composeViews vlist =
  let sourceSyms = symbols $ source (head vlist)
   in zip sourceSyms $ List.map (mapSymbol vlist) sourceSyms 

-- EDNOTE: head and last
-- this function is called after guard is checked
computeCombine :: [View] -> Mapping -> [View] -> Mapping -> (Theory,View,View)
computeCombine path1 ren1 path2 ren2 =
  let map1 = composeViews path1 ++ ren1
      map2 = composeViews path2 ++ ren2 
      commonSrc = source $ head path1
      dest1 = target $ last path1
      dest2 = target $ last path2
      -- EDNOTE: use the functions instead 
      (Theory (ParamDecl pars) (Fields flds)) = applyMapping commonSrc map1 -- rename, while taking care of the theory structure. Name of target thry does not matter here, but its structure does. 
      (Theory (ParamDecl parsDest1) (Fields fldsDest1)) = applyMapping (dest1) map1 
      (Theory (ParamDecl parsDest2) (Fields fldsDest2)) = applyMapping (dest2) map2
      newFlds = flds ++ (fldsDest1 List.\\ flds) ++ (fldsDest2 List.\\ flds)
      newParams = pars ++ (parsDest1 List.\\ pars) ++ (parsDest2 List.\\ pars)
      newThry = Theory (ParamDecl newParams) (Fields newFlds)
      view1 = View dest1 newThry map1 
      view2 = View dest2 newThry map2 
  in (newThry,view1,view2) 

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

pairToFunc :: Mapping -> RenameFunc 
pairToFunc list elem = if result == [] then elem
                       else if (length result) == 1 then head result
                       else error "Multiple mappings for the same symbol" 
  where result = Prelude.map snd $ Prelude.filter (\x -> fst x ==  elem) list 

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
