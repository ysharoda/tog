module Tog.TGraphState where

import Tog.TGraph
import Tog.TGraphTest 
import Tog.Raw.Abs
import Tog.PrettyPrint as PP 

import Control.Monad.State
import qualified Data.Map as Map

printTGraphWState :: PP.Doc 
printTGraphWState = printModule $ snd $ runState pmgraphState initGraph 

data ModExpr' =
  Extend' Theory [SConstr]
  | Rename' Theory InputMap
  | Combine' Theory InputMap Theory InputMap CommonSubStruc 

newtype CommonSubStruc = Over Theory 

theory :: Name_ -> ModExpr' -> State TGraph Theory
theory name (Extend' thry strDecls) = extend name thry (map parseConstr strDecls)
theory name (Rename' thry imapp) = rename name thry imapp
theory name (Combine' th1 ren1 th2 ren2 (Over srcThry))  =
  combine name (TMPair th1 $ Map.fromList ren1)
               (TMPair th2 $ Map.fromList ren2) srcThry 
  
extend :: Name_ -> Theory -> [Constr] -> State TGraph Theory 
extend name thry decls =
  state $ \graph ->
    (extThry decls thry,
     updateGraph graph name (Left $ computeExtend decls thry)) 

rename :: Name_ -> Theory -> InputMap -> State TGraph Theory
rename name thry rens =
  state $ \graph ->
    (applyMapping thry $ rensMap ,
     updateGraph graph name (Left $ computeRename rensMap thry)) 
  where rensMap = Map.fromList rens    

-- Theory - Mapping Pair 
data TMPair = TMPair Theory Mapping 

combine :: Name_ -> TMPair -> TMPair -> Theory -> State TGraph Theory 
combine name (TMPair th1 ren1) (TMPair th2 ren2) srcThry =
  state $ \graph ->
    ((resThry graph),updateGraph graph name (Right $ utri graph))  
  where
    qpath graph thry ren = QPath (getPath graph srcThry thry) ren
    utri graph = computeCombine (qpath graph th1 ren1) (qpath graph th2 ren2) 
    resThry graph = getDest (utri graph)



pmgraphState :: State TGraph Theory 
pmgraphState =
  do
    carrier <- theory "Carrier" $ Extend' emptyThry ["A : Set"]
    magma   <- theory "Magma"   $ Extend' carrier ["op : A -> A -> A"]
    pointed <- theory "Pointed" $ Extend' carrier ["e : A"]
    -- pointedMagma <- theory "PointedMagma" $ Combine' magma [] pointed [] (Over carrier)
    additiveMagma <- theory "AdditiveMagma" $ Rename' magma [("A","Nat"),("op","plus")]
    pointed0 <- theory "Pointed0" $ Rename' pointed [("A","Nat"),("e","0")]
    theory "AddPointedMagma" $ Combine' additiveMagma [] pointed0 [] (Over carrier)  

