module Interpret.Deriving.GenEverything where

import           Tog.Raw.Abs           as Abs
import qualified Interpret.Deriving.EqTheory as Eq
import           Interpret.Utils.TypeConversions
import           Interpret.Deriving.Hom
import           Interpret.Deriving.ProductTheory
import           Interpret.Deriving.Signature
import           Interpret.Deriving.RelationalInterp
import           Interpret.Deriving.Terms
import           Interpret.Deriving.Evaluator
import           Interpret.Deriving.Simplifier
import           Interpret.Deriving.Induction 
import           Interpret.Deriving.StagedTerms
import           Interpret.Deriving.Tagless

leverageThry :: Eq.EqTheory -> [Decl]
leverageThry thry =
 let
     sigs = (sigToDecl . signature_) thry
     prodthry = (prodTheoryToDecl . productThry) thry
     hom = homomorphism thry
     relInterp = relationalInterp thry 
     trmLangs = termLangs thry
     temLangsDecls = termLangsToDecls trmLangs
     simplifiers = simplifyFuncs thry trmLangs 
     evaluators = evalFuncs thry trmLangs
     inductions = inductionFuncs trmLangs
     stagedTLs = stagedFuncs trmLangs
     tagless = taglessRep thry 
 in
     [sigs, prodthry, hom, relInterp] 
     ++ temLangsDecls 
     ++  simplifiers
     ++ evaluators
     ++ inductions
     ++ stagedTLs ++ [tagless] 

genEverything :: Decl -> Decl
genEverything m@(Module_ (Module n p (Decl_ decls))) =
  Module_ $ Module n p (Decl_ $ decls ++ (concatMap leverageThry $ getEqTheories m)) 
genEverything x = x  
