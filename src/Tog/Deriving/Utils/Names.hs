module Tog.Deriving.Utils.Names (ren) where

import Tog.Raw.Abs 
import Tog.Deriving.Lenses (name)
import Tog.Deriving.TUtils (mkName)

import Control.Lens ((^.))

-- renames sn to newName and adds suffix "L" to all other names. 
ren :: String -> (String,String) -> Name -> Name
ren sn (newName,suffix) n = mkName $ if (nam == sn) then newName else nam ++ suffix
  where nam = n^.name
