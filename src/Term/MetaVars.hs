{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.MetaVars where

import           Prelude.Extended
import           Term.Types

instance IsTerm t => Metas t (Clause t) where
  metas (Clause _ t) = metas t

instance IsTerm t => Metas t (Invertible t) where
  metas (NotInvertible clauses) = metas clauses
  metas (Invertible injClauses) = metas $ map snd injClauses

instance (Metas t a, Metas t b) => Metas t (a, b) where
  metas (x, y) = (<>) <$> metas x <*> metas y

instance IsTerm t => Metas t (Definition t) where
  metas (Constant t c)         = metas (t, c)
  metas (DataCon _ _ type_)    = metas type_
  metas (Projection _ _ type_) = metas type_

instance IsTerm t => Metas t (Constant t) where
  metas Postulate           = return mempty
  metas (Data _)            = return mempty
  metas (Record _ _)        = return mempty
  metas (Instantiable inst) = metas inst

instance (IsTerm t) => Metas t (Inst t) where
  metas Open     = return mempty
  metas (Inst t) = metas t

instance Metas t a => Metas t (Maybe a) where
  metas Nothing  = return mempty
  metas (Just x) = metas x

instance Metas t (Signature t) where
  metas sig =
    metas $ map (sigGetDefinition sig) (sigDefinedNames sig)

instance Metas t (Tel t) where
  metas T0                  = return mempty
  metas ((_, type_) :> tel) = metas (type_, tel)

instance (IsTerm t, Metas t a) => Metas t (Contextual t a) where
  -- TODO can't we just ignore `x'?
  metas (Contextual x y) = metas (x, y)

