 {-# LANGUAGE UnicodeSyntax #-}

module Interpret.Exporting.AgdaPredStyle where

import Tog.Raw.Abs

import Interpret.Flattener.Types
import Interpret.Utils.TypeConversions (getEqTheories, theoryToRecord)
import Interpret.Utils.Utils (isSort, isFunc, isAxiom)
import Interpret.Utils.TUtils (mkName, mkArg, strToDecl)  
import Interpret.Deriving.GenEverything (leverageThry)
import Interpret.Deriving.TogPrelude (prelude)

import Control.Lens ((^.))
import qualified Data.Map as Map

makeInnerModules :: Map.Map Name_ GTheory -> [Decl]
makeInnerModules theories =
  (map strToDecl prelude) ++ 
  (Map.elems $ Map.mapWithKey agdaPredModule theories)

agdaPredModule :: Name_ -> GTheory -> Decl 
agdaPredModule thryName thry =
  let flatDecl = theoryToRecord thryName thry
      eqThryList = getEqTheories flatDecl 
      generated = if length eqThryList == 1 then leverageThry $ head eqThryList else [] 
  in if (length (thry ^. declarations) <= 1)
     then Module_ $ Module (mkName thryName) NoParams $ Decl_ [flatDecl] 
     else Module_ $ Module (mkName thryName) NoParams $
            Decl_ $ [theoryToRecord ("Is"++thryName) (isX thry),
                     theoryToRecord thryName (adjustTheory thryName thry)]
                    ++ generated

{-
makeOneBigModule :: Map.Map Name_ GTheory -> Module
makeOneBigModule theories =
  Module (mkName "Mathscheme") NoParams $
    Decl_ $ (map strToDecl prelude) ++ (makeInnerModules theories) 

-}
-- ------------------------------------- 

notAxiom, axiom :: [Constr] -> [Constr]
notAxiom constrs = filter (\(Constr _ e) -> (isSort e || isFunc e)) constrs
axiom constrs = filter (\(Constr _ e) -> isAxiom e) constrs

isX :: GTheory -> GTheory
isX (GTheory constrs _) =
  let newWaist = length (notAxiom constrs) 
  in GTheory (notAxiom constrs ++ axiom constrs) newWaist

{-
-- need to also figure our which params should be passed
-- i.e. check the morphism mappings  
backwardMorph :: TGraph -> GTheory -> GTheory   
backwardMorph tg thry = 
  let directAncestors = [v | v <- ((Map.elems $ tg^.edges), target v == thry]
  in 
-}

-- the new theory with a class to IsX 
adjustTheory :: Name_ -> GTheory -> GTheory
adjustTheory thryName (GTheory constrs wst) =
  let isXName = "Is"++thryName
      fsyms = notAxiom constrs
      fsymNames = map (\(Constr (Name (_,nm)) _) -> nm) fsyms
      processName n = if elem n ["+","-","*"] then "("++n++")" else n 
      callIsX = [Constr (mkName $ "is"++thryName)
                   (App $ (mkArg isXName) : (map (mkArg . processName) fsymNames))]
  in GTheory (fsyms ++ callIsX) wst 

