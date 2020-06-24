-- Lenses from Tog AST pieces
{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.Lenses
  ( name
  , cExpr
  ) where

import Control.Lens
import Tog.Deriving.PConstr 

import Tog.Raw.Abs 

name :: Lens' Name String
name = lens (\(Name (_,s)) -> s) (\(Name x) s -> Name (fst x, s))

cExpr :: Lens' PConstr Expr
cExpr = lens (\(PConstr _ e _) -> e) (\(PConstr x _ b) e' -> PConstr x e' b)
