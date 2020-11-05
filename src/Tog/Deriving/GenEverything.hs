module Tog.Deriving.GenEverything where

import           Tog.Raw.Abs           as Abs
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.TypeConversions
import           Tog.Deriving.Hom
import           Tog.Deriving.ProductTheory
import           Tog.Deriving.Signature
import           Tog.Deriving.RelationalInterp
import           Tog.Deriving.Terms
import           Tog.Deriving.Evaluator
import           Tog.Deriving.Simplifier
import           Tog.Deriving.Induction 
import           Tog.Deriving.StagedTerms
import           Tog.Deriving.Tagless

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
