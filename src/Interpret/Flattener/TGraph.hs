module Interpret.Flattener.TGraph
  ( lookupName
  , updateGraph
  , computeExtend
  , computeRename
  , getPath
  , computeCombine
  , addArrow
  , findApex 
  ) where

import qualified Data.Generics      as Generics
import qualified Data.List          as List
import qualified Data.Map           as Map
import qualified Data.List.NonEmpty as NE

import Control.Lens (over, (^.))

import           Tog.Raw.Abs
import           Interpret.Utils.TUtils
import           Interpret.Flattener.Types

type RenameFunc = Name_ -> Name_



{- ------------------- Build the Graph  ----------------- -}
  
updateGraph ::   Name_ -> Either GView PushOut -> TGraph -> TGraph
updateGraph nm (Left view) =
  over nodes (Map.insert nm (target view)) .
  over edges (Map.insert ("To"++nm) view)

-- TODO: find a way to get the name of the source theory. 
updateGraph nm (Right ut) =
   over nodes (Map.insert nm (target $ uLeft ut)) .
   over edges (\e -> foldr (uncurry Map.insert) e 
                        [("To"++nm++"1",uLeft ut),
                         ("To"++nm++"2",uRight ut),
                         ("To"++nm++"D",diagonal ut)])

{- ------------------- Elaborate Into TheoryGraph ---------------- -}

-- --------- RENAME -----------
computeRename :: Rename -> GTheory -> GView  
computeRename namesMap thry =
  GView thry (renameThy thry namesMap) (validateRen thry namesMap)

-- --------- EXTENSION ---------
computeExtend :: [Constr] -> GTheory -> GView
computeExtend newDecls srcThry =
  GView srcThry (extThry newDecls srcThry) (validateRen srcThry Map.empty)
            
extThry :: [Constr] -> GTheory -> GTheory 
extThry newConstrs thry@(GTheory constrs wst) =
  if List.intersect newConstrNames (symbols thry) == []
  then GTheory (constrs ++ newConstrs) wst
  -- (newParams (params thry)) $ newFields (fields thry) -- TODO: Decl added to param?
  else error $ "Cannot create theory "
  where newConstrNames = map getConstrName newConstrs
 {-     sorts = filter (\(Constr _ e) -> isSort e) newConstrs
        notSorts = newConstrs List.\\ sorts
        newParams NoParams = if sorts == [] then NoParams else ParamDecl $ map fldsToBinding sorts
        newParams (ParamDecl ps) = ParamDecl (ps ++ map fldsToBinding sorts)
        newParams _ = NoParams 
        newFields NoFields = if (notSorts == []) then NoFields else Fields newConstrs
        newFields (Fields fs) = Fields (fs ++ notSorts)
-}
-- ----------- Arrow -------------
addArrow :: Name_ -> GView -> TGraph -> TGraph
addArrow nm arrow =
  over edges (\g -> (Map.insert nm arrow g))  

-- ----------- COMBINE -----------

computeCombine :: QPath -> QPath -> PushOut
computeCombine qpath1 qpath2 =
  let isTriangle = (qpathSource qpath1) == (qpathSource qpath2)
   in if (not isTriangle)
      then error "The two theories do not meet at the source"
      else if (not $ checkGuards qpath1 qpath2)
      then error "Name Clash!"         
      else createDiamond qpath1 qpath2

findApex :: TGraph -> GTheory -> GTheory -> GTheory
findApex grph thry1 thry2 =
  let empty = lookupName "Empty" grph
      [p1,p2] = map (NE.toList . theoriesOntheWay . getPath grph empty) [thry1,thry2]
      common = List.intersect p1 p2
  in if (common == []) then error "No common source found"
     else last common
          
theoriesOntheWay :: Path -> NE.NonEmpty GTheory
theoriesOntheWay p =
  NE.cons (source $ NE.head p) (NE.map target p) 

-- Precondition: Called after checkGuards
createDiamond :: QPath -> QPath -> PushOut
createDiamond left right =
 let commonSrc = qpathSource left
     lt = qpathTarget left
     rt = qpathTarget right
     lp = path left
     rp = path right
     lren = ren left
     rren = ren right
     lThry = applyCompositeRename lt lp lren
     rThry = applyCompositeRename rt rp rren
     srcMapped = applyCompositeRename commonSrc lp lren
     newThry = GTheory (disjointUnion3 (srcMapped^.declarations) (lThry^.declarations) (rThry^.declarations)) (srcMapped^.waist)
     allMaps qp = composeMaps $ (map (\(GView _ _ m) -> m) $ NE.toList $ path qp) ++ [ren qp]
     lView = GView lt newThry $ validateRen lt (allMaps left)
     rView = GView rt newThry $ validateRen rt (allMaps right)
     diag  = GView commonSrc newThry $ validateRen commonSrc (allMaps left)
  in pushout lView rView diag

getPath :: TGraph -> GTheory -> GTheory -> Path 
getPath graph src trgt =
  let p =  getPath' (Map.elems $ graph^.edges) src trgt
  in case p of { [] -> error $ "no path found from " ++ lookupTheory src graph ++ " to " ++ lookupTheory trgt graph ; _ -> NE.fromList p}

getPath' :: [GView] -> GTheory -> GTheory -> [GView] 
getPath' edgesList src dest =
  let viewsToDest = [v | v <- edgesList, target v == dest]
      answer = filter (\v -> source v == src) viewsToDest
      found = case answer of
                []    -> [(getPath' edgesList src (source v)) ++ [v] | v <- viewsToDest]
                (x:_) -> [[x]]
      p = List.filter (\ls -> (source $ NE.head (NE.fromList ls)) == src) found
   in case p of { [] -> [] ; (x : _) -> x }

{- ------------------------ Utils --------------------------------- -}

lookupName :: Name_ -> TGraph -> GTheory
lookupName name graph =
  case (Map.lookup name $ graph^.nodes) of
    Nothing -> error $ name ++ "is not a valid theory name"
    Just t  -> t

lookupTheory :: GTheory -> TGraph -> Name_
lookupTheory thry grph =
  case Map.toList $ Map.filter (== thry) (grph^.nodes) of
    [] -> "theory not found"
    [(k,_)] -> k
    _ -> error "A theory has more than one name" 

qpathSource :: QPath -> GTheory
qpathSource = source . NE.head . path

qpathTarget :: QPath -> GTheory
qpathTarget = target . NE.last . path

renameThy :: GTheory -> Rename -> GTheory
renameThy (GTheory constrs wst) m =
  GTheory (gmap (mapAsFunc m) constrs) wst
         -- (gmap (mapAsFunc m) (fields thry))

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
      allUnique xs = List.nub xs == xs 
   in allUnique (map fst relevantMaps) &&
      allUnique (map snd relevantMaps) &&
      List.intersect (map snd relevantMaps) syms == []

-- turns a rename list into an injective mapping over the symbols of the source theory. 
validateRen :: GTheory -> Rename -> Rename
validateRen srcThry m =
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
composeMaps = foldr composeTwoMaps Map.empty

mapAsFunc :: Rename -> RenameFunc 
mapAsFunc r = \x -> Map.findWithDefault x x r

{- ------------------------------------------------ -} 
{-
getArgs :: Params -> [Arg]
getArgs NoParams = []
getArgs (ParamDef _) = [] 
getArgs (ParamDecl binds) = concatMap getBindingArgs binds
-}
symbols :: GTheory -> [Name_]
symbols thry =
  let declNames = Generics.listify (\(Constr (Name (_, _)) _) -> True) thry
  in map getConstrName declNames

checkGuards :: QPath -> QPath -> Bool
checkGuards qpath1 qpath2 =
  let sameSource = (qpathSource qpath1) == (qpathSource qpath2)
      symsMapped qp = symbols $ applyCompositeRename (qpathSource qp) (path qp) (ren qp) 
      trgtSyms1 = symsMapped qpath1
      trgtSyms2 = symsMapped qpath2
   in if (sameSource &&
      trgtSyms1 == trgtSyms2) then True else error $ "Name Clash! between " ++ (show trgtSyms1) ++ " and " ++ (show trgtSyms2) 
