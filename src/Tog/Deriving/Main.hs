module Tog.Deriving.Main
  ( processDefs
  , declRecords 
  ) where

import qualified Data.Map              as Map
import           Control.Lens (view)

import           Tog.Raw.Abs           as Abs
import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.Hom
import           Tog.Deriving.TGraphTest 
import           Tog.Deriving.ProductTheory
import           Tog.Deriving.Signature 
import           Tog.Deriving.TypeConversions
import           Tog.Deriving.Types
import           Tog.Deriving.TUtils  (mkName, setType,strToDecl)
import           Tog.Deriving.RelationalInterp
import           Tog.Deriving.Terms
import           Tog.Deriving.Evaluator
--import           Tog.Deriving.OpenTermEvaluator
import           Tog.Deriving.TogPrelude (prelude)
import           Tog.Deriving.Simplifier
import           Tog.Deriving.Induction 
--import           Tog.Deriving.StagedTerms
--import           Tog.Deriving.Tagless 

processDefs :: [Language] -> Module
processDefs = processModule . defsToModule

defsToModule :: [Language] -> Module
defsToModule = createModules . view (graph . nodes) . computeGraph

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
   Module n p $ Decl_ $
     (prodType : map strToDecl prelude) 
      ++ map genEverything decls   
processModule _ = error $ "Unparsed theory expressions exists" 

leverageThry :: Eq.EqTheory -> [Decl]
leverageThry thry =
 let sigs = (sigToDecl . signature_) thry
     prodthry = (prodTheoryToDecl . productThry) thry
     hom = homomorphism thry
     relInterp = relationalInterp thry
     trmLangs = termLangs thry
     temLangsDecls = termLangsToDecls trmLangs
     simplifiers = simplifyFuncs thry trmLangs
     evaluators = evalFuncs thry trmLangs
     inductions = inductionFuncs thry trmLangs 
 --    trmlang = termLang thry
 --    openTrmLang = openTermLang thry
 --    evalTrmLang = evalFunc thry
 --    evalOpenTrmLang = openEvalFunc thry 
 --    simplifier = simplifyFunc thry
 --    stagedClosedTerms = liftTermCl thry
 --    stagedOpenTerms = liftTermOp thry
 --    tagless = taglessRep thry  
 in [sigs, prodthry, hom, relInterp] ++ temLangsDecls ++ simplifiers ++ evaluators ++ inductions 
    
    --[trmlang, openTrmLang] ++ evalTrmLang ++ evalOpenTrmLang ++ simplifier ++
    --stagedClosedTerms ++ stagedOpenTerms ++ [tagless] 

genEverything :: InnerModule -> InnerModule
genEverything m@(Module_ (Module n p (Decl_ decls))) =
  Module_ (Module n p (Decl_ $
    -- [strToDecl "open NatNum ; open Prelude ; "] ++ 
    decls ++
    (concatMap leverageThry $ getEqTheories m)))
genEverything x = x  

{- ------- Filtering the EqTheories ------------ -} 

type InnerModule = Decl

getEqTheories :: InnerModule -> [Eq.EqTheory]
getEqTheories (Module_ (Module _ _ (Decl_ decls))) =
  map recordToEqTheory $ 
    filter (not . isEmptyTheory) $ concatMap declRecords decls
getEqTheories x = map recordToEqTheory $ declRecords x

declRecords :: Decl -> [TRecord]
declRecords (Record n p r) = [TRecord n p r]
declRecords (Module_ (Module _ _ (Decl_ decls))) = concatMap declRecords decls 
declRecords _ = []

isEmptyTheory :: TRecord -> Bool 
isEmptyTheory (TRecord _ NoParams (RecordDecl _)) = True
isEmptyTheory (TRecord _ NoParams (RecordDef  _ NoFields)) = True
isEmptyTheory (TRecord _ NoParams (RecordDeclDef _ _ NoFields)) = True
isEmptyTheory _ = False

{- ------------------------------------------------------------- -} 

mathscheme :: Name
mathscheme = mkName "MathScheme" 

theoryToRecord :: Name_ -> GTheory -> Decl 
theoryToRecord n (GTheory ps fs) =
  Record (mkName n) ps (RecordDeclDef setType (mkName $ n++"C") fs)  

recordToModule :: Name_ -> Decl -> Decl
recordToModule n record =
  Module_ $ Module (mkName n) NoParams $ Decl_ [record] 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module mathscheme NoParams $ Decl_ $ Map.elems modules 

{-
[TypeSig (Sig (Name ((1,20),"inductionOpE")) (Pi (Tel [Bind [Arg (Id (NotQual (Name ((1,20),"n"))))] (App [Arg (Id (NotQual (Name ((1,20),"Nat"))))]),Bind [Arg (Id (NotQual (Name ((1,20),"A"))))] (App [Arg (Id (NotQual (Name ((1,20),"Set"))))]),Bind [Arg (Id (NotQual (Name ((1,20),"P"))))] (Fun (App [Arg (Id (NotQual (Name ((1,20),"OpMonoidTerm2")))),Arg (Id (NotQual (Name ((1,20),"n")))),Arg (Id (NotQual (Name ((1,20),"A"))))]) (App [Arg (Id (NotQual (Name ((1,20),"Set"))))]))]) (Fun (Pi (Tel [HBind [Arg (Id (NotQual (Name ((1,20),"x1"))))] (App [Arg (Id (NotQual (Name ((1,20),"A"))))])]) (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (App [Arg (Id (NotQual (Name ((1,20),"sing2")))),Arg (Id (NotQual (Name ((1,20),"x1"))))])])) (Fun (Pi (Tel [HBind [Arg (Id (NotQual (Name ((1,20),"fin"))))] (App [Arg (Id (NotQual (Name ((1,20),"Fin")))),Arg (Id (NotQual (Name ((1,20),"n"))))])]) (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (App [Arg (Id (NotQual (Name ((1,20),"v2")))),Arg (Id (NotQual (Name ((1,20),"fin"))))])])) (Fun (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (App [Arg (Id (NotQual (Name ((1,20),"eOL2"))))])]) (Fun (Pi (Tel [HBind [Arg (Id (NotQual (Name ((1,20),"x1")))),Arg (Id (NotQual (Name ((1,20),"x2"))))] (App [Arg (App [Arg (Id (NotQual (Name ((1,20),"OpMonoidTerm2")))),Arg (Id (NotQual (Name ((1,20),"n")))),Arg (Id (NotQual (Name ((1,20),"A"))))])])]) (Fun (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (Id (NotQual (Name ((1,20),"x1"))))]) (Fun (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (Id (NotQual (Name ((1,20),"x2"))))]) (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (App [Arg (Id (NotQual (Name ((1,20),"opOL2")))),Arg (Id (NotQual (Name ((1,20),"x1")))),Arg (Id (NotQual (Name ((1,20),"x2"))))])])))) (Pi (Tel [Bind [Arg (Id (NotQual (Name ((1,20),"x"))))] (App [Arg (Id (NotQual (Name ((1,20),"OpMonoidTerm2")))),Arg (Id (NotQual (Name ((1,20),"n")))),Arg (Id (NotQual (Name ((1,20),"A"))))])]) (App [Arg (Id (NotQual (Name ((1,20),"P")))),Arg (App [Arg (Id (NotQual (Name ((1,20),"x"))))])])))))))),


 FunDef (Name ((1,20),"inductionOpE"))
  [IdP (NotQual (Name ((1,20),"p"))),
   IdP (NotQual (Name ((1,20),"pv2"))),
   IdP (NotQual (Name ((1,20),"psing2"))),
   IdP (NotQual (Name ((1,20),"peol2"))),
   IdP (NotQual (Name ((1,20),"popol2"))),
   ConP (NotQual (Name ((1,20),"v2"))) [IdP (NotQual (Name ((1,20),"x1")))]]
  (FunDefBody (Id (NotQual (Name ((1,20),"pv2")))) NoWhere),

 FunDef (Name ((1,20),"inductionOpE"))
 [IdP (NotQual (Name ((1,20),"p"))),
  IdP (NotQual (Name ((1,20),"pv2"))),
  IdP (NotQual (Name ((1,20),"psing2"))),
  IdP (NotQual (Name ((1,20),"peol2"))),
  IdP (NotQual (Name ((1,20),"popol2"))),
  ConP (NotQual (Name ((1,20),"sing2"))) [IdP (NotQual (Name ((1,20),"x1")))]]
  (FunDefBody (Id (NotQual (Name ((1,20),"psing2")))) NoWhere),

 FunDef (Name ((1,20),"inductionOpE"))
 [IdP (NotQual (Name ((1,20),"p"))),
  IdP (NotQual (Name ((1,20),"pv2"))),
  IdP (NotQual (Name ((1,20),"psing2"))),
  IdP (NotQual (Name ((1,20),"peol2"))),
  IdP (NotQual (Name ((1,20),"popol2"))),
  IdP (NotQual (Name ((1,20),"eOL2")))]
  (FunDefBody (Id (NotQual (Name ((1,20),"peol2")))) NoWhere),

 FunDef (Name ((1,20),"inductionOpE"))
 [IdP (NotQual (Name ((1,20),"p"))),
  IdP (NotQual (Name ((1,20),"pv2"))),
  IdP (NotQual (Name ((1,20),"psing2"))),
  IdP (NotQual (Name ((1,20),"peol2"))),
  IdP (NotQual (Name ((1,20),"popol2"))),
  ConP (NotQual (Name ((1,20),"opOL2"))) [IdP (NotQual (Name ((1,20),"x1"))),IdP (NotQual (Name ((1,20),"x2")))]]
  (FunDefBody
   (App [Arg (Id (NotQual (Name ((1,20),"opOL2")))),
         Arg (App [Arg (Id (NotQual (Name ((1,20),"inductionOpE")))),
                   Arg (Id (NotQual (Name ((1,20),"P")))),
                   Arg (Id (NotQual (Name ((1,20),"pv2")))),
                   Arg (Id (NotQual (Name ((1,20),"psing2"))))
                  ,Arg (Id (NotQual (Name ((1,20),"peol2")))),
                   Arg (Id (NotQual (Name ((1,20),"popol2")))),
                   Arg (Id (NotQual (Name ((1,20),"x1"))))]),
          Arg (App [Arg (Id (NotQual (Name ((1,20),"inductionOpE")))),
                    Arg (Id (NotQual (Name ((1,20),"P")))),
                    Arg (Id (NotQual (Name ((1,20),"pv2")))),
                    Arg (Id (NotQual (Name ((1,20),"psing2")))),
                    Arg (Id (NotQual (Name ((1,20),"peol2")))),
                    Arg (Id (NotQual (Name ((1,20),"popol2")))),
                    Arg (Id (NotQual (Name ((1,20),"x2"))))])]) NoWhere)]
-}
