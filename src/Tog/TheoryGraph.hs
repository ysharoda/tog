{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}
module TheoryGraph where

import Data.Map as Map

import Tog.Raw.Abs
import Tog.Utils

import Control.Lens
import Data.Map as Map 
import Data.Generics
import Data.Data
import qualified Data.List as List


data Theory = Theory{
                tname   :: String,
                params :: Params,
                fields :: Fields }  deriving (Eq, Ord, Show, Read, Typeable, Data)

$(makeLenses ''Theory)

data View   = View{
                vname   :: String,
                source :: Theory,
                target :: Theory,
                map    :: [(String,String)] }  deriving (Eq, Ord, Show, Read, Typeable, Data)

data TGraph = TGraph{
                nodes :: Map String Theory,
                edges :: Map String View }  deriving (Eq, Ord, Show, Read, Typeable, Data)

type Mapping = [(String,String)] 
type RenameFunc = String -> String

data ModExpr = Rename Theory Mapping
--             | Extends Theory [Constr]
--             | Combine Theory Theory Theory

-- ------------ Building Theory Graph ----------------------------

addThryToGraph :: TGraph -> Theory -> TGraph 
addThryToGraph tg thry =
  if Map.lookup (tname thry) (nodes tg) == Nothing
  then TGraph (insert (tname thry) thry (nodes tg)) (edges tg)
  else tg 

addViewToGraph :: TGraph -> View -> TGraph
addViewToGraph (TGraph n e) v = TGraph n (insert (vname v) v e) 

-- ---------------------------------------------------------------

pairToFunc :: [(String,String)] -> String -> String
pairToFunc list elem = if result == [] then elem
                       else if (length result) == 1 then head result
                       else error "Multiple mappings for the same symbol" 
  where result = Prelude.map snd $ Prelude.filter (\x -> fst x ==  elem) list 

symbols :: Theory -> [String]
symbols thry =
  let 
    getArgs NoParams = []
    getArgs (ParamDef _) = [] 
    getArgs (ParamDecl bindsList) = Prelude.foldr (++) [] $ Prelude.map getBindingArgs bindsList 
    argNames   = everything (++) (mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) (getArgs $ params thry)    
    fieldNames = everything (++) (mkQ [] (\(Constr (Name (_,n)) _) -> [n])) thry 
  in argNames ++ fieldNames 


-- allUnique snds --> no two symbols mapped to the same name
-- allUnique fsts --> no symbol mapped to two different names
-- noConflist --> The new names do not occur in the theory
checkNameConflict :: [(String,String)] -> Theory -> Bool
checkNameConflict namesMap thry =
  let fsts = Prelude.map fst namesMap 
      snds = Prelude.map snd namesMap      
      nonIdMaps  = Prelude.filter (\(x,y) -> x /= y) namesMap
      noConflict = List.intersect (symbols thry) (Prelude.map snd nonIdMaps) == []
      allUnique xs = List.nub xs == xs 
   in allUnique snds && allUnique fsts && noConflict


-- ------------------ rename combinator ---------------------------

renThry :: [(String,String)] -> Theory -> Theory 
renThry list theory = everywhere (mkT $ pairToFunc list) theory


renameMap :: [(String,String)] -> Theory -> [(String,String)] 
renameMap list thry = zip syms $ Prelude.map (pairToFunc list) syms
        where syms = symbols thry


rename :: [(String,String)] -> Theory -> (View,Theory)  
rename namesMap theory = 
    let target = renThry namesMap theory
        view = renameMap namesMap theory 
     in (View "n" theory target view, target)        

-- ----------------------------------------------------------------

-- -------------------- example ------------------------------

noSrcLoc :: (Int,Int)
noSrcLoc = (0,0)




constructPM :: String -> String -> String -> String -> Theory
constructPM name carrier unit op =
         Theory name
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [Constr (Name (noSrcLoc,unit))
                                (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)]),
                         Constr (Name (noSrcLoc,op))
                                (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)])
                                     (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)])
                                          (App [Arg $ Id $ NotQual $ Name (noSrcLoc,carrier)])))])


pointedMagma, addPM :: Theory 
pointedMagma = constructPM "PointedMagma" "A" "e" "op"
addPM = constructPM "AddPM" "N" "0" "plus"

additive :: View
additive = View "additive" pointedMagma addPM [("A","N"),("e","0"),("op","plus")]

simpleGraph :: TGraph 
simpleGraph =
  let graph = TGraph Map.empty Map.empty
      n = nodes graph
      e = edges graph
  in TGraph (insert (tname addPM) addPM (insert (tname pointedMagma) pointedMagma n)) (insert (tname $ target additive) additive e)  


