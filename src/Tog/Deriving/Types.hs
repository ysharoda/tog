module Tog.Deriving.Types
  ( Name_ , Path, Rename
  , GTheory(..)
  , GView(..)
  , QPath(..)
  , TGraph(..)
  , PushOut( uLeft, uRight, diagonal, apex), pushout
  ) where

import qualified Data.Generics      as Generics
import qualified Data.List.NonEmpty as NE
import qualified Data.Map           as Map

import           Tog.Raw.Abs
import           Tog.DerivingInsts ()  -- for instances of Tog AST

type Name_ = String
type Path  = NE.NonEmpty GView
type Rename = Map.Map Name_ Name_

data GTheory = GTheory {
    params :: Params,
    fields :: Fields }
  deriving (Eq, Ord, Show, Generics.Typeable, Generics.Data)

data GView   = GView {
    source  :: GTheory,
    target  :: GTheory,
    rename :: Rename }  
  deriving (Eq, Ord, Show, Generics.Typeable, Generics.Data)

data QPath = QPath { -- Qualified path, i.e. a path with a rename
    path :: Path,
    ren  :: Rename } deriving Show 

data TGraph = TGraph { -- check if I would rather use only a map of edges
    nodes :: Map.Map Name_ GTheory,
    edges :: Map.Map Name_ GView } 
  deriving (Eq, Ord, Show, Generics.Typeable, Generics.Data)

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

