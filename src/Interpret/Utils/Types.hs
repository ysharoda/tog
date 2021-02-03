module Interpret.Utils.Types where

import Tog.Raw.Abs
import Interpret.Utils.TUtils 
import Interpret.Utils.Bindings (indexBindings, getBindingsNames, hiddenBind)
import Interpret.Utils.Lenses (name)

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

type DTInstance = (Name_,[Binding],Expr) 

tinstance :: DTDef -> Maybe Int -> DTInstance 
tinstance (Data nm NoParams _) _ = (shortName (nm^.name) 0,[],App [mkArg $ nm ^. name])
tinstance (Data nm (ParamDecl binds) _) Nothing =
  let names = getBindingsNames binds 
  in (shortName (nm^.name) 0, binds,App $ (mkArg (nm ^. name)) : map mkArg names)  
tinstance (Data nm (ParamDecl binds) _) (Just i) =
  let newBinds = map hiddenBind $ indexBindings i binds
      names = getBindingsNames newBinds 
  in (shortName (nm^.name) i,binds,App $ (mkArg (nm ^. name)) : map mkArg names) 
tinstance _ _ = error "unable to generate data type application" 
