module Tog.Deriving.Utils.Variables where

import Tog.Raw.Abs
import Tog.Deriving.Types (Name_) 
import Tog.Deriving.TUtils (mkQName) 

varPattern :: Name_ -> Pattern
varPattern x = IdP (mkQName x) 

