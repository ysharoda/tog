module Tog.Deriving.TGraph where

import qualified Data.Generics      as Generics
import qualified Data.List          as List
import qualified Data.Map           as Map
import qualified Data.List.NonEmpty as NE

import           Tog.Raw.Abs
import           Tog.Deriving.Utils
import           Tog.Deriving.Types

type RenameFunc = Name_ -> Name_

{- ------------------- Build the Graph  ----------------- -}
  
updateGraph ::  TGraph -> Name_ -> Either GView PushOut -> TGraph
updateGraph graph newThryName (Left view) =
  TGraph (Map.insert newThryName (target view) $ nodes graph)
         (Map.insert ("To"++newThryName) view  $ edges graph)
-- TODO: find a way to get the name of the source theory. 
updateGraph graph newThryName (Right ut) =
   TGraph (Map.insert newThryName (target $ uLeft ut) $ nodes graph)
        $ (Map.fromList [("To"++newThryName++"1",uLeft ut),
                         ("To"++newThryName++"2",uRight ut),
                         ("To"++newThryName++"D",diagonal ut)])
          `Map.union` (edges graph)

{- ------------------- Elaborate Into TheoryGraph ---------------- -}

computeTransport :: Rename -> GTheory -> GView
computeTransport rmap thry =
  GView thry (renameThy thry rmap)
        (injectiveRename rmap thry)   

-- --------- RENAME -----------
computeRename :: Rename -> GTheory -> GView  
computeRename namesMap srcThry =
  GView srcThry (renameThy srcThry namesMap)
       (injectiveRename namesMap srcThry)

-- --------- EXTENSION ---------
computeExtend :: [Constr] -> GTheory -> GView
computeExtend newDecls srcThry =
  GView srcThry (extThry newDecls srcThry)
       (injectiveRename Map.empty srcThry)
            
extThry :: [Constr] -> GTheory -> GTheory 
extThry newConstrs thry =
  if List.intersect newConstrNames (symbols thry) == []
  then GTheory (params thry) $ newFields (fields thry) -- TODO: Decl added to param?
  else error $ "Cannot create theory "
  where newConstrNames = constrsNames newConstrs
        newFields NoFields = Fields newConstrs
        newFields (Fields fs) = Fields (fs ++ newConstrs)

-- ----------- COMBINE ----------- 
computeCombine :: QPath -> QPath -> PushOut
computeCombine qpath1 qpath2 =
  let isTriangle = (qpathSource qpath1) == (qpathSource qpath2)
   in if (not isTriangle)
      then error "The two theories do not meet at the source"
      else if (not $ checkGuards qpath1 qpath2)
      then error "Name Clash!"         
      else createDiamond qpath1 qpath2 
   
-- Precondition: Called after checkGuards
createDiamond :: QPath -> QPath -> PushOut
createDiamond left right =
 let commonSrc = qpathSource left
     lThry = applyCompositeRename (qpathTarget left)  (path left)  (ren left)
     rThry = applyCompositeRename (qpathTarget right) (path right) (ren right)
     srcMapped = applyCompositeRename commonSrc (path left) (ren left)
     newThry =
       GTheory (ParamDecl $ disjointUnion3 (getParams $ params srcMapped) (getParams $ params lThry) (getParams $ params rThry))
               (Fields    $ disjointUnion3 (getFields $ fields srcMapped) (getFields $ fields lThry) (getFields $ fields rThry))
     allMaps qp = composeMaps $ (map (\(GView _ _ m) -> m) $ NE.toList $ path qp) ++ [ren qp]
     lView = GView (qpathTarget left)  newThry $ injectiveRename (allMaps left) (qpathTarget left)
     rView = GView (qpathTarget right) newThry $ injectiveRename (allMaps right) (qpathTarget right) 
     diag  = GView commonSrc newThry $ injectiveRename (allMaps left) commonSrc   
  in pushout lView rView diag

getPath :: TGraph -> GTheory -> GTheory -> Path 
getPath graph src trgt =
  let p =  getPath' (Map.elems $ edges graph) src trgt
  in if p /= []
     then NE.fromList p
     else error "no path found"

getPath' :: [GView] -> GTheory -> GTheory -> [GView] 
getPath' edgesList src dest =
  let answer = [v | v <- edgesList, target v == dest, source v == src]
      viewsToDest = [v | v <- edgesList, target v == dest]
      found = if answer /= [] then [[head answer]]
              else [(getPath' edgesList src (source v)) ++ [v] | v <- viewsToDest]
      p = List.filter (\ls -> (source $ NE.head (NE.fromList ls)) == src) found             
   in if p == []
      then [] 
      else List.head p 

{- ------------------------ Utils --------------------------------- -}

lookupName :: Name_ -> TGraph -> GTheory
lookupName name graph =
  case (Map.lookup name $ nodes graph) of
    Nothing -> error $ name ++ "is not a valid theory name"
    Just t  -> t

qpathSource :: QPath -> GTheory
qpathSource = source . NE.head . path

qpathTarget :: QPath -> GTheory
qpathTarget = target . NE.last . path

constrsNames :: [Constr] -> [Name_]
constrsNames constrs = map (\(Constr (Name (_, n)) _) -> n) constrs 

renameThy :: GTheory -> Rename -> GTheory
renameThy thry m =
  GTheory (gmap (mapAsFunc m) (params thry)) 
          (gmap (mapAsFunc m) (fields thry))

applyCompositeRename :: GTheory -> Path -> Rename -> GTheory
applyCompositeRename thry pth rena =
  renameThy thry $
     composeMaps $ (map (\(GView _ _ m) -> m) $ NE.toList $ pth) ++ [rena]
     
-- allUnique snds --> no two symbols mapped to the same name
-- allUnique fsts --> no symbol mapped to two different names
-- noConflist --> The new names do not occur in the theory
validRename :: Rename -> GTheory -> Bool
validRename namesMap thry =
  let syms = symbols thry 
      relevantMaps = [(k,a) | (k,a) <- Map.toList namesMap, k `elem` syms, k/=a]
      noConflict = List.intersect (map snd relevantMaps) syms == []
      allUnique xs = List.nub xs == xs 
   in allUnique (map fst relevantMaps) && allUnique (map snd relevantMaps) && noConflict

-- turns a rename list into an injective mapping over the symbols of the source theory. 
injectiveRename :: Rename -> GTheory -> Rename
injectiveRename m srcThry =
  if validRename m srcThry
  then Map.fromList $ List.map (\x -> (x, mapAsFunc m x)) $ symbols srcThry
  else error $ "cannot apply rename " ++ (show (Map.toList m)) ++ " to theory with symbols " ++ show (symbols srcThry) 

disjointUnion3 :: Eq a => [a] -> [a] -> [a] ->  [a]
disjointUnion3 l1 l2 l3 = l1 ++ (l2 List.\\ l1) ++ (l3 List.\\ l1)


{- -------- Composing Maps ----------- -}

-- The list representation of Maps
-- The algorithm is weird because empty maps are identity maps
composeTwoMaps :: Rename -> Rename -> Rename
composeTwoMaps m1 m2 = 
  let k1 = Map.keys m1
      k2 = Map.keys m2
      -- all the things only renamed in m2
      k3 = k2 List.\\ k1
      updateFrom m k m' = maybe m' (\v -> Map.insert k v m') (Map.lookup k m)
      -- initialize from the keys k3 in m2
      m3 = foldr (updateFrom m2) Map.empty k3 in
  -- and then insert all that is in m1, looking up in m2 and defaulting
  Map.foldrWithKey (\k a m -> Map.insert k (Map.findWithDefault a k m2) m) m3 m1

composeMaps :: [Rename] -> Rename
composeMaps mapsList = foldr composeTwoMaps Map.empty mapsList

mapAsFunc :: Rename -> RenameFunc 
mapAsFunc m = \x -> Map.findWithDefault x x m

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

checkGuards :: QPath -> QPath -> Bool
checkGuards qpath1 qpath2 =
  let sameSource = (qpathSource qpath1) == (qpathSource qpath2)
      symsMapped qp = symbols $ applyCompositeRename (qpathSource qp) (path qp) (ren qp) 
      trgtSyms1 = symsMapped qpath1
      trgtSyms2 = symsMapped qpath2
   in if (sameSource &&
      trgtSyms1 == trgtSyms2) then True else error $ "Name Clash! between " ++ (show trgtSyms1) ++ " and " ++ (show trgtSyms2) 
