module TheoryGraph where

import Tog.Raw.Abs
import Tog.Utils
 
import qualified Data.Generics as Generics
import qualified Data.List     as List


data Theory = Theory{
                tname   :: String,
                params :: Params,
                fields :: Fields }
              deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)


data View   = View{
                vname   :: String,
                source  :: Theory,
                target  :: Theory,
                mapping :: [(String,String)] }
             deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

data TGraph = TGraph{
                nodes :: [Theory],
                edges :: [View] }  deriving (Eq, Ord, Show, Read, Generics.Typeable, Generics.Data)

type Mapping = [(String,String)] 
type RenameFunc = String -> String

data ModExpr = Rename String Theory Mapping
               | Extends Theory [Constr]
               | Combine Theory Theory Mapping Theory Mapping 


-- ------------------ Rename Combinator ---------------------------

renThry :: String -> [(String,String)] -> Theory -> Theory 
renThry newName list theory = 
  Generics.everywhere (Generics.mkT $ pairToFunc newList) theory
  where newList = (tname theory,newName) : list 


renameMap :: [(String,String)] -> Theory -> [(String,String)] 
renameMap list thry = zip syms $ Prelude.map (pairToFunc list) syms
        where syms = symbols thry


rename :: String -> [(String,String)] -> Theory -> (View,Theory)  
rename newThryName namesMap theory =
  if noNameConflict namesMap theory 
  then   let targetThry = renThry newThryName namesMap theory
             view = renameMap namesMap theory 
         in (View "n" theory targetThry view, targetThry)        
  else error "rename cannot be applied"

-- -------------- Extends Combinator -----------------------------

extThry :: String -> Theory -> [Constr] -> Theory
extThry newName thry@(Theory n pars (Fields fs)) newConstrs =
  let newDeclNames = Prelude.map (\(Constr n _) -> nameToStr n) newConstrs 
      noConflict = freshNames newDeclNames thry 
  in if (noConflict) then Theory newName pars $ Fields (fs ++ newConstrs)
                     else error $ "Cannot create theory " ++ newName

extends :: String -> Theory -> [Constr] -> (View,Theory)  
extends newThryName oldThry newDecls =
  let newThry = extThry newThryName oldThry newDecls
      thrySyms = symbols oldThry
      idMap = zip thrySyms thrySyms
      newView = View "ext" oldThry newThry idMap 
   in (newView,newThry) 

-- --------------------- Combine ----------------------------------


path :: TGraph -> Theory -> Theory -> [View] 
path graph src dest =
  let edgs = edges graph
      answer = [v | v <- edgs, target v == dest, source v == src]
      viewsToDest = [v | v <- edgs, target v == dest]
      found = if answer /= [] then [[head answer]]
              else [(path graph src (source v)) ++ [v] | v <- viewsToDest] 
  in Prelude.head $ Prelude.filter (\ls -> (source (head ls)) == src) found

mapSymbol :: [View] -> String -> String
mapSymbol lview sym =
  let getMappings = List.concat $ List.map (\v -> mapping v) lview
      findMatch [] x = x
      findMatch ((f,s):fs) x =
          if (x == f) then findMatch fs s else findMatch fs x 
   in findMatch getMappings sym -- Prelude.foldr (.) strId $ List.map pairToFunc getMappings   

getViews :: TGraph -> Theory -> Theory -> Theory -> ([View],[View]) 
getViews graph src dest1 dest2 =
   let path1 = path graph src dest1
       path2 = path graph src dest2
   in  (path1,path2) 

checkGuard :: [View] -> [View] -> Bool
checkGuard path1 path2 =
  let nonEmptyPaths = path1 /= [] && path2 /= [] 
      srcThry = if (source (head path1)) == (source (head path2)) then source (head path1) else error "invalid arrows"
      srcSyms = symbols srcThry
   in nonEmptyPaths &&
      (List.map (mapSymbol path1) srcSyms) == (List.map (mapSymbol path1) srcSyms)


composeViews :: [View] -> Mapping
composeViews vlist =
  let sourceSyms = symbols $ source (head vlist)
   in zip sourceSyms $ List.map (mapSymbol vlist) sourceSyms
{-      targetThry = (target $ last vlist)
   in if (((List.map snd newMapping) `List.intersect` (symbols targetThry)) /= (List.map snd newMapping))
      then error "Views do not compose properly"
      else View newName (source $ head vlist) targetThry newMapping -}

applyView :: String -> Theory -> Mapping -> Theory 
applyView newName thry mapp =
      Theory newName 
             (Generics.everywhere (Generics.mkT $ pairToFunc mapp) (params thry)) 
             (Generics.everywhere (Generics.mkT $ pairToFunc mapp) (fields thry)) 

-- this function is called after guard is checked

computeCombine :: String -> [View] -> Mapping -> [View] -> Mapping -> (View,View,Theory)
computeCombine newThryName path1 ren1 path2 ren2 =
  let map1 = composeViews path1 ++ ren1
      map2 = composeViews path2 ++ ren2 
      src = source $ head path1
      dest1 = target $ last path1
      dest2 = target $ last path2 
      (Theory _ (ParamDecl pars) (Fields flds)) = applyView "X" src map1
      (Theory _ (ParamDecl parsDest1) (Fields fldsDest1)) = applyView "Y" (dest1) map1 
      (Theory _ (ParamDecl parsDest2) (Fields fldsDest2)) = applyView "Z" (dest2) map2
      newFlds = flds ++ (fldsDest1 List.\\ flds) ++ (fldsDest2 List.\\ flds)
      newParams = pars ++ (parsDest1 List.\\ pars) ++ (parsDest2 List.\\ pars)
      newThry = Theory newThryName (ParamDecl newParams) (Fields newFlds)
      view1 = View (tname dest1 ++ "To" ++ tname newThry) dest1 newThry map1 
      view2 = View (tname dest2 ++ "To" ++ tname newThry) dest2 newThry map2 
  in (view1,view2,newThry) 

combine :: TGraph -> String -> String -> String -> Mapping -> String -> Mapping -> (View,View,Theory)
combine graph newThryName srcName d1Name ren1 d2Name ren2 =
  let getTheory thryName = List.find (\x -> tname x == thryName) (nodes graph)
      theories = [getTheory srcName, getTheory d1Name, getTheory d2Name] 
  in  if elem Nothing theories
      then error "One or more theory does not exist"
      else let Just src   = theories !! 0
               Just dest1 = theories !! 1
               Just dest2 = theories !! 2
               (path1,path2) = getViews graph src dest1 dest2
            in if checkGuard path1 path2
               then computeCombine newThryName path1 ren1 path2 ren2
               else error "Cannot compute the expr" 
     
-- ----------------------------------------------------------------

-- ------------------------ Helper Functions -------------------------

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
    argNames   = Generics.everything (++) (Generics.mkQ [] (\(Id (NotQual (Name (_,n)))) -> [n])) (getArgs $ params thry)    
    fieldNames = Generics.everything (++) (Generics.mkQ [] (\(Constr (Name (_,n)) _) -> [n])) thry 
  in argNames ++ fieldNames 


freshNames :: [String] -> Theory -> Bool
freshNames newNames thry =
  List.intersect newNames (symbols thry) == []

-- allUnique snds --> no two symbols mapped to the same name
-- allUnique fsts --> no symbol mapped to two different names
-- noConflist --> The new names do not occur in the theory
noNameConflict :: [(String,String)] -> Theory -> Bool
noNameConflict namesMap thry =
  let fsts = Prelude.map fst namesMap 
      snds = Prelude.map snd namesMap      
      nonIdMaps  = Prelude.filter (\(x,y) -> x /= y) namesMap
      noConflict = freshNames (Prelude.map snd nonIdMaps) thry 
      allUnique xs = List.nub xs == xs 
   in allUnique snds && allUnique fsts && noConflict

-- ----------------------------------------------------------------



-- ------------ Building Theory Graph ----------------------------

addThryToGraph :: TGraph -> Theory -> TGraph 
addThryToGraph tg thry =
  if not $ elem thry (nodes tg)
  then TGraph ((nodes tg) ++ [thry]) (edges tg)
  else tg 

addViewToGraph :: TGraph -> View -> TGraph
addViewToGraph (TGraph n e) v = TGraph n (e ++ [v])

extendGraph :: TGraph -> ModExpr -> TGraph
extendGraph tg (Rename newName thry mapping) =
  let (vnew,tnew) = rename newName mapping thry
   in addViewToGraph (addThryToGraph tg tnew) vnew 

-- -------------------- example ------------------------------

recordToTheory :: Decl -> Theory 
recordToTheory (Record n par (RecordDef _ f)) =
  Theory (nameToStr n) par f 
recordToTheory _ = error "The input is not a valid theory"          




noSrcLoc :: (Int,Int)
noSrcLoc = (0,0)


carrier = Theory "Carrier" 
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [])

magma =  Theory "Magma"
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [Constr (Name (noSrcLoc,"op"))
                                (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])
                                     (Fun (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])
                                          (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])))])

pointed = Theory "Pointed"
                (ParamDecl [Bind [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")]
                                 (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"Set")])])
                (Fields [Constr (Name (noSrcLoc,"e"))
                                (App [Arg $ Id $ NotQual $ Name (noSrcLoc,"A")])])

carrierToMagma = View "carrierToMagma" carrier magma [("A","A")]
carrierToPointed = View "carrierToPointed" carrier pointed [("A","A")]

diamond = TGraph [carrier,magma,pointed] [carrierToMagma,carrierToPointed]
                

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


pointedMagma, addPM, multPM :: Theory 
pointedMagma = constructPM "PointedMagma" "A" "e" "op"
addPM = constructPM "AddPM" "A" "0" "plus"
multPM = constructPM "multPM" "N" "1" "mult" 

additive :: View
additive = View "additive" pointedMagma addPM [("A","A"),("e","0"),("op","plus")]

fakeMultiplicative :: View
fakeMultiplicative = View "fakeMultiplicative" addPM multPM [("A","N"),("0","1"),("plus","mult")]

simpleGraph :: TGraph 
simpleGraph =
  let graph = TGraph [] [] 
      n = nodes graph
      e = edges graph
  in TGraph [pointedMagma, addPM, multPM] [additive, fakeMultiplicative] 


