{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.TGraphTest
  ( computeGraph 
  , graph
  ) where

import qualified Data.Map            as Map
import           Control.Lens ((^.), makeLenses, over)

import           Tog.Deriving.Lenses (name)
import           Tog.Deriving.Types
import           Tog.Deriving.TGraph
import           Tog.Raw.Abs         as Abs

data Library = Library {
  _graph   :: TGraph,
  _mappings :: Map.Map Name_ Rename }

makeLenses ''Library

initLibrary :: Library 
initLibrary = Library emptyTG (Map.empty)

waistNm :: Int 
waistNm = 1 

computeGraph :: [Abs.Language] ->  Library 
computeGraph = foldl add initLibrary

add :: Library -> Abs.Language -> Library
add lib (TheoryC nm clist)  = theory  nm clist lib
add lib (MappingC nm vlist) = addMapping nm vlist lib
add lib (ModExprC nm mexps) = modExpr nm mexps lib

theory :: Name -> [Abs.Constr] -> Library -> Library
theory nm cList =
  let newThry  = GTheory cList waistNm
  in  over graph (over nodes (Map.insert (nm^.name) newThry))

addMapping :: Name -> [RenPair] -> Library -> Library
addMapping nm rens = 
  over mappings (Map.insert (nm^.name) (renPairsToMapping rens))

getTheory :: Library -> Name -> GTheory
getTheory gs n = lookupName (n^.name) (gs^.graph)

modExpr :: Name -> Abs.ModExpr -> Library -> Library
modExpr nam mexpr lib =
  let n = nam^.name
      look = getTheory lib
      rens = findRename lib
      combineOver t1 r1 t2 r2 s =
        let gr = lib^.graph
            p1 = getPath gr s t1
            p2 = getPath gr s t2
            qpath1 = QPath p1 $ rens r1
            qpath2 = QPath p2 $ rens r2
        in over graph
           (updateGraph n $ Right $ computeCombine qpath1 qpath2) lib    
  in case mexpr of
    Extend srcName clist ->
      over graph
        (updateGraph n $ Left $ computeExtend clist (look srcName)) lib
    Rename srcName rlist ->   
      over graph
        (updateGraph n $ Left $ computeRename (rens rlist) (look srcName)) lib
    RenameUsing srcName nm ->
     let mapin = (lib^.mappings) Map.! (nm^.name) 
     in over graph
        (updateGraph n $ Left $ computeRename mapin (look srcName))
        lib
    CombineOver t1 r1 t2 r2 srcName ->
     let s = look srcName
     in combineOver (look t1) r1 (look t2) r2 s 
    Combine t1 t2 ->
     let s = findApex (lib^.graph) (look t1) (look t2)
     in combineOver (look t1) NoRens (look t2) NoRens s
    Transport t1 t2 -> 
     let s = findApex (lib^.graph) (look t1) (look t2)
     in combineOver (look t1) NoRens (look t2) NoRens s
    Arrow src dest maps ->
     over graph (addArrow n $ GView (look src) (look dest) (rens maps)) lib

renPairsToMapping :: [RenPair] -> Rename
renPairsToMapping rplist = Map.fromList $ map (\(RenPair x y) -> (x^.name,y^.name)) rplist 

rensToMappings :: Rens -> Rename
--rensToMappings (NameRens n) = (gs^.mappings) Map.! (n^.name)
rensToMappings NoRens = Map.empty
rensToMappings (Rens rlist) = Map.fromList $ map (\(RenPair x y) -> (x^.name,y^.name)) rlist

findRename :: Library -> Rens -> Rename
findRename lib (NameRens n) = (lib^.mappings) Map.! (n^.name)
findRename _ x = rensToMappings x
