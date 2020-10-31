module Tog.Deriving.Main
  ( processDefs
  , theoryToRecord
  , defsToModule
  , leverageThry
  ) where

import qualified Data.Map              as Map
import           Control.Lens (view)

import           Tog.Raw.Abs           as Abs
-- import qualified Tog.Deriving.EqTheory as Eq
import           Tog.Deriving.TGraphTest 
import           Tog.Deriving.TypeConversions
import           Tog.Deriving.Types
import           Tog.Deriving.TUtils  (mkName, strToDecl)
import           Tog.Deriving.TogPrelude (prelude)
import           Tog.Deriving.GenEverything

import           Tog.Exporting.AgdaStdLib (makeOneBigModule)

data OperatingMode = Generate | AgdaStdLibLike 

operatingMode :: OperatingMode
operatingMode = Generate 

processDefs :: [Language] -> Module
processDefs =
  case operatingMode of
    Generate -> processModule . defsToModule
    AgdaStdLibLike -> (defsToModule_agdaStdlibLike)

defsToModule :: [Language] -> Module
defsToModule = createModules . view (graph . nodes) . computeGraph

{- -------- the agda like version --------- -} 
defsToModule_agdaStdlibLike :: [Language] -> Module
defsToModule_agdaStdlibLike =
  makeOneBigModule . view (graph . nodes) . computeGraph

{- ---------------------------------------- -}   
  

processModule :: Module -> Module
processModule (Module n p (Decl_ decls)) =
   Module n p $ Decl_ $
       (map strToDecl prelude) ++ 
       map genEverything decls   
processModule _ = error "Unparsed theory expressions exists" 

{- ------------------------------------------------------------- -} 

mathscheme :: Name
mathscheme = mkName "MathScheme" 

createModules :: Map.Map Name_ GTheory -> Abs.Module
createModules theories =
  let records = Map.mapWithKey theoryToRecord theories
      modules = Map.mapWithKey recordToModule records 
  in Module mathscheme NoParams $ Decl_ $ Map.elems modules 


