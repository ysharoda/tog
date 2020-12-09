module Tog.Deriving.Main
  ( processDefs
  , theoryToRecord
  , defsToModule
  , leverageThry
  , theories 
  ) where

import qualified Data.Map              as Map
import           Control.Lens (view)

import           Tog.Raw.Abs           as Abs
import           Tog.Deriving.TGraphTest 
import           Tog.Deriving.TypeConversions
import           Tog.Deriving.Types
import           Tog.Deriving.TUtils  (mkName, strToDecl)
import           Tog.Deriving.TogPrelude (prelude)
import           Tog.Deriving.GenEverything

processDefs :: [Language] -> Module
processDefs = processModule . defsToModule

defsToModule :: [Language] -> Module
defsToModule = createModules . theories

theories :: [Language] -> Map.Map Name_ GTheory
theories = view (graph . nodes) . computeGraph

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
createModules thrs =
  let records = Map.mapWithKey theoryToRecord thrs
      modules = Map.mapWithKey recordToModule records 
  in Module mathscheme NoParams $ Decl_ $ Map.elems modules 


