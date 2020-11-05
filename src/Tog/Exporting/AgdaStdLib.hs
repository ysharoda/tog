 {-# LANGUAGE UnicodeSyntax #-}

module Tog.Exporting.AgdaStdLib where

import Tog.Raw.Abs
import Tog.Deriving.Types
import Tog.Deriving.TypeConversions (getEqTheories, theoryToRecord)
import Tog.Deriving.Utils (isSort, isFunc, isAxiom)
import Tog.Deriving.TUtils (mkName, mkArg, strToDecl)  
import Tog.Deriving.GenEverything (leverageThry)
import Tog.Deriving.TogPrelude (prelude)
import qualified Data.Map as Map
import Control.Lens ((^.))

{-
import Tog.Deriving.Lenses (name)
import Tog.Deriving.Utils.Bindings (getBindingArgs, getBindingExpr)
import Tog.Deriving.TUtils (getArgExpr, getArgName, getName) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen as PP 
import Data.Generics hiding (Constr, empty)

import Data.List.Split (splitOn)
import Data.Char (toUpper)
-}
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
adjustTheory :: Name_ -> GTheory -> GTheory
adjustTheory thryName (GTheory constrs wst) =
  let isXName = "Is"++thryName
      fsyms = notAxiom constrs
      fsymNames = map (\(Constr (Name (_,nm)) _) -> nm) fsyms
      processName n = if elem n ["+","-","*"] then "("++n++")" else n 
      callIsX = [Constr (mkName $ "is"++thryName)
                   (App $ (mkArg isXName) : (map (mkArg . processName) fsymNames))]
  in GTheory (fsyms ++ callIsX) wst 

createTheoryModule :: Name_ -> GTheory -> Decl 
createTheoryModule thryName thry =
  let flatDecl = theoryToRecord thryName thry
      eqThryList = getEqTheories flatDecl 
      generated = if length eqThryList == 1 then leverageThry $ head eqThryList else [] 
  in if (length (thry ^. declarations) <= 1) then flatDecl 
     else Module_ $ Module (mkName thryName) NoParams $
            Decl_ $ [theoryToRecord ("Is"++thryName) (isX thry),
                     theoryToRecord thryName (adjustTheory thryName thry)]
                    ++ generated

makeInnerModules :: Map.Map Name_ GTheory -> [Decl]
makeInnerModules theories =
  Map.elems $ Map.mapWithKey createTheoryModule theories

makeOneBigModule :: Map.Map Name_ GTheory -> Module
makeOneBigModule theories =
  Module (mkName "Mathscheme") NoParams $
    Decl_ $ (map strToDecl prelude) ++ (makeInnerModules theories) 


