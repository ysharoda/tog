module Tog.Deriving.Utils.Types where

import Tog.Raw.Abs
import Tog.Deriving.TUtils 
import Tog.Deriving.Utils.Bindings (indexBindings, getBindingsNames, )

import Tog.Deriving.Lenses (name)
import Control.Lens ((^.))

-- Utils on Pi Types
getPiExpr :: Expr -> Expr
getPiExpr (Pi _ expr) = expr
getPiExpr _ = error "not a Pi type" 

getPiBinds :: Expr -> [Binding]
getPiBinds (Pi (Tel binds) _) = binds
getPiBinds _ = error "not a Pi type" 

-- a representation of a datatype
type DTDef = Decl

type DTInst = ([Binding],Expr) 

tinstance :: DTDef -> Maybe Int -> DTInst 
tinstance (Data nm NoParams _) _ = ([],App [mkArg $ nm ^. name])
tinstance (Data nm (ParamDecl binds) _) Nothing =
  let names = getBindingsNames binds 
  in (binds,App $ (mkArg (nm ^. name)) : map mkArg names)  
tinstance (Data nm (ParamDecl binds) _) (Just i) =
  let newBinds = indexBindings True i binds
      names = getBindingsNames newBinds 
  in (binds,App $ (mkArg (nm ^. name)) : map mkArg names) 
tinstance _ _ = error "unable to generate data type application" 
