{-# LANGUAGE TemplateHaskell #-}
module Tog.Deriving.Types
  ( Name_ , Path
  , Rename
  , gmap -- generic map
  , GTheory(..)
  , GView(..)
  , QPath(..)
  , TGraph, nodes, edges, emptyTG
  , PushOut( uLeft, uRight, diagonal, apex), pushout
  ) where

import qualified Data.Generics      as Generics
import qualified Data.List.NonEmpty as NE
import qualified Data.Map           as Map

import Control.Lens (makeLenses)

import           Tog.Raw.Abs
import           Tog.DerivingInsts ()  -- for instances of Tog AST

type Name_ = String
type Path  = NE.NonEmpty GView
type Rename = Map.Map Name_ Name_

gmap :: (Generics.Typeable a, Generics.Data b) => (a -> a) -> b -> b
gmap r x = Generics.everywhere (Generics.mkT r) x

-- Eq is needed in building 'pushout' below
data GTheory = GTheory {
    params :: Params,
    fields :: Fields }
  deriving (Show, Eq, Generics.Typeable, Generics.Data)

data GView   = GView {
    source  :: GTheory,
    target  :: GTheory,
    rename :: Rename }  
  deriving (Generics.Typeable, Generics.Data)

data QPath = QPath { -- Qualified path, i.e. a path with a rename
    path :: Path,
    ren  :: Rename }

data TGraph = TGraph { -- check if I would rather use only a map of edges
    _nodes :: Map.Map Name_ GTheory,
    _edges :: Map.Map Name_ GView } 
  deriving (Generics.Typeable, Generics.Data)

makeLenses ''TGraph

emptyTG :: TGraph
emptyTG = TGraph Map.empty Map.empty

-- Pushouts
data PushOut = PushOut { -- of a span
   uLeft    :: GView,
   uRight   :: GView,
   diagonal :: GView,
   apex     :: GTheory } -- common point

pushout :: GView -> GView -> GView -> PushOut
pushout v1 v2 diag =
  if (target v1 == target v2) && (target v2 == target diag) 
  then PushOut v1 v2 diag (target diag)
  else error "Views have different targets"

