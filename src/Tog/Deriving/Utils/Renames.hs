module Tog.Deriving.Utils.Renames where

import Tog.Raw.Abs 
import Tog.Deriving.Lenses (name)
import Tog.Deriving.TUtils (mkName,getConstrName)
import Tog.Deriving.EqTheory
import Tog.Deriving.Types (gmap)

import Control.Lens ((^.))

-- renames sn to newName and adds suffix "L" to all other names. 
ren :: String -> (String,String) -> Name -> Name
ren sn (newName,suffix) n = mkName $ if (nam == sn) then newName else nam ++ suffix
  where nam = n^.name

applyRenames :: EqTheory -> (String,String) -> [Constr] 
applyRenames eq (nm,suff) =
  gmap (ren (getConstrName $ eq^.sort) (nm,suff)) $ eq^.funcTypes  

ren' :: String -> (String,String) -> Name -> Name
ren' sn (newName,suffix) n = mkName $ if (nam == sn) then newName else suffix
  where nam = n^.name

foldren :: EqTheory -> [(String,String)] -> EqTheory
foldren eq [] = eq 
foldren eq ((old,new):rens) =
  foldren (gmap (\x -> if x == old then new else x) eq) rens 
