module Tog.Deriving.Utils.Types where

import Tog.Raw.Abs

-- Utils on Pi Types
getPiExpr :: Expr -> Expr
getPiExpr (Pi _ expr) = expr
getPiExpr _ = error "not a Pi type" 

getPiBinds :: Expr -> [Binding]
getPiBinds (Pi (Tel binds) _) = binds
getPiBinds _ = error "not a Pi type" 
