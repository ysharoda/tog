module TheoryGraph where

import Tog.Raw.Abs
import Tog.Utils
 
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
    mapping :: Mapping } -- change this mapping too 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data TGraph = TGraph{ -- check is I would rather use only a map of edges
    nodes :: Map.Map Name_ Theory,
    edges :: Map.Map Name_ View } 
  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

type Name_ = String
type Path  = [View]
type RenameFunc = String -> String
type Mapping = [(String,String)] -- Mapping (Map.Map Name_ Name_) 


data ModExpr = Rename Name_ Theory Mapping
               | Extends Name_ Theory [Constr]
               | Combine Name_ Path Mapping Path Mapping
               -- not the export the constructor at the outside of the module 

-- 
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


-- ----------------------------------------------------------------


-- ------------ Building Theory Graph ----------------------------
{-
getTheoryFromName :: [Theory] -> Name_ -> Theory
getTheoryFromName thryList thryName =
  let thry = List.find (\x -> tname x == thryName) thryList
  in case thry of
        Just x  -> x
        Nothing -> error "theory does not exist" 
  
addThryToGraph :: Theory -> TGraph -> TGraph 
addThryToGraph thry tg =
  if not $ elem thry (nodes tg)
  then TGraph ((nodes tg) ++ [thry]) (edges tg)
  else tg 

addViewToGraph :: View -> TGraph -> TGraph 
addViewToGraph v (TGraph n e) = TGraph n (e ++ [v])

elaborateExpr :: TGraph -> ModExpr -> TGraph
elaborateExpr tgraph (Rename newThryName srcThry renMap) =
  let (newT,newV) = rename newThryName renMap srcThry
  in  addThryToGraph newT $ addViewToGraph newV tgraph 
elaborateExpr tgraph (Extends newThryName srcThry newDecls) =
  let (newT,newV) = extends newThryName newDecls srcThry  
  in  addThryToGraph newT $ addViewToGraph newV tgraph 
elaborateExpr tgraph (Combine newThryName view1 renMap1 view2 renMap2) =
  let (newT,v1,v2) = computeCombine newThryName view1 renMap1 view2 renMap2
  in  (addThryToGraph newT $ 
         addViewToGraph v2 $ 
           addViewToGraph v1 tgraph)

-}
      
                  {-

combine :: TGraph -> Name_ -> Name_ -> Name_ -> Mapping -> Name_ -> Mapping -> (Theory,View,View)
combine graph newThryName srcName d1Name ren1 d2Name ren2 =

computeCombine :: Name_ -> [View] -> Mapping -> [View] -> Mapping -> (Theory,View,View)
computeCombine newThryName path1 ren1 path2 ren2 =

data ModExpr = Rename String Theory Mapping
               | Extends Theory [Constr]
               | Combine Theory Theory Mapping Theory Mapping 

-}

-- -------------------- example ------------------------------

recordToTheory :: Decl -> Theory 
recordToTheory (Record n par (RecordDef _ f)) =
  Theory par f 
recordToTheory _ = error "The input is not a valid theory"          




noSrcLoc :: (Int,Int)
noSrcLoc = (0,0)


carrier = Theory 
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [])

magma =  Theory 
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [Constr (Name (noSrcLoc,"op"))
                                (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])
                                     (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])
                                          (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])))])

pointed = Theory
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [Constr (Name (noSrcLoc,"e"))
                                (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])])

carrierToMagma = View carrier magma [("A","A")]
carrierToPointed = View carrier pointed [("A","A")]

diamond = TGraph (Map.fromList [("Carrier",carrier),("Magma",magma),("Pointed",pointed)])
                 (Map.fromList [("CarrierToMagma",carrierToMagma),("CarrierToPointed",carrierToPointed)])
                

constructPM :: String -> String -> String -> String -> Theory
constructPM name carrier unit op =
         Theory
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [Constr (Name (noSrcLoc,unit))
                                (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)]),
                         Constr (Name (noSrcLoc,op))
                                (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)])
                                     (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)])
                                          (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)])))])


pointedMagma, addPM, multPM :: Theory 
pointedMagma = constructPM "PointedMagma" "A" "e" "op"
addPM = constructPM "AddPM" "A" "0" "plus"
multPM = constructPM "multPM" "N" "1" "mult" 

additive :: View
additive = View pointedMagma addPM [("A","A"),("e","0"),("op","plus")]

fakeMultiplicative :: View
fakeMultiplicative = View addPM multPM [("A","N"),("0","1"),("plus","mult")]

simpleGraph :: TGraph 
simpleGraph =
  let graph = TGraph Map.empty Map.empty  
      n = nodes graph
      e = edges graph
  in TGraph (Map.fromList [("PointedMagma",pointedMagma), ("AdditivePM",addPM), ("MultiplicativePM",multPM)])
            (Map.fromList [("additive",additive), ("fakeMultiplicative",fakeMultiplicative)])


