module Interpret.Deriving.Main
  ( processDefs
  , processModule
  , theoryToRecord
  , defsToModule
  , leverageThry
  , theories 
  ) where

import qualified Data.Map              as Map
import           Control.Lens (view)

import           Tog.Raw.Abs           as Abs
import           Interpret.Flattener.Main 
import           Interpret.Utils.TypeConversions
import           Interpret.Flattener.Types
import           Interpret.Utils.TUtils  (mkName, strToDecl)
import           Interpret.Deriving.TogPrelude (prelude)
import           Interpret.Deriving.GenEverything

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


