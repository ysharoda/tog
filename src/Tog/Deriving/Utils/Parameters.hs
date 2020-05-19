-- The Parameters of the hom record 
module Tog.Deriving.Utils.Parameters where 

import Control.Lens ((^.))

import Tog.Raw.Abs 
import Tog.Deriving.TUtils
import Tog.Deriving.Types (Name_)
import Tog.Deriving.Lenses   (name)
import Tog.Deriving.EqTheory 

-- the hidden params 
recordParams :: ([Arg] -> Expr -> Binding) -> Constr -> Binding
recordParams bind (Constr nm typ) =
  let n = nm^.name in bind [mkArg' n 1, mkArg' n 2] typ

-- two instances of the EqTheory record 
createThryInsts :: EqTheory -> ((Binding, Name_), (Binding, Name_))
createThryInsts t =
  let nam = t ^. thyName
      (n1, n2) = (twoCharName nam 1, twoCharName nam 2) in
  ((Bind [mkArg n1] (declTheory nam (args t) 1), n1) ,
   (Bind [mkArg n2] (declTheory nam (args t) 2), n2) )
