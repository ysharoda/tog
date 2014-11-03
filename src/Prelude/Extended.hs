{-# LANGUAGE CPP #-}

module Prelude.Extended
  ( Foldable
  , Traversable
  , Hashable(..)
  , (<*>)
  , Applicative
  , (<>)
  , (<$>)
  , (>=>)
  , (<=<)
  , Typeable
  , Generic
  , fromMaybe
  , pure
  , join
  , foldl'
  , liftM
  , when
  , void
  , guard
  , mzero
  , forM
  , msum
  , unless
  , first
  , forM_
  , on
  , sortBy
  , groupBy
  , isJust
  , comparing
  , traverse
  , (<$)
  , sequenceA
  , lift
  , trace
  , traceM
  , (<|>)
  , ap
  , IsString(..)
  , (***)
  , second
  , isNothing
  , Monoid(..)
  , mplus
  , any
  , MonadIO(..)
  , foldlM
  , Bwd(..)
  , toList
 , fold
  , intersperse
  , isPrefixOf
  , for
  , elemIndex
  ) where

import Prelude ()

import Control.Applicative
import Control.Arrow
import Control.Monad hiding (forM_, msum, forM)
import Control.Monad.IO.Class
import Data.Foldable
import Data.Function
import Data.Hashable
import Data.List hiding (foldl', any)
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Traversable
import Data.Typeable
import GHC.Generics
import Control.Monad.Trans
import Debug.Trace
import Data.String
import Data.Bwd

#if __GLASGOW_HASKELL__ >= 708
#else
traceM :: (Monad m) => String -> m ()
traceM string = trace string $ return ()
#endif
