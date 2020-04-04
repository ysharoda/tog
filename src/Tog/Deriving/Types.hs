module Tog.Deriving.Types where

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

