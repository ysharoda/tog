-- Lenses from Tog AST pieces
{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.Lenses
  ( name
  ) where

import Control.Lens

import Tog.Raw.Abs 

name :: Lens' Name String
name = lens (\(Name (_,s)) -> s) (\(Name x) s -> Name (fst x, s))
