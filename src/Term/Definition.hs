{-# LANGUAGE OverloadedStrings #-}
module Term.Definition
    ( -- * 'Clause'
      Clause(..)
    , ClauseBody
    , instantiateClauseBody
    , Pattern(..)
    , patternBindings
    , patternsBindings
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
    , TermHead(..)
    , Invertible(..)
    , ignoreInvertible
    , mapInvertible
    ) where

import           Bound                            (Bound, (>>>=), Var(B, F))
import qualified Bound.Name                       as Bound
import           Bound.Scope.Simple               (Scope(Scope), fromScope)
import           Control.Arrow                    (second)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (Void, absurd)
import           Prelude.Extras                   (Eq1, (==#))

import           Syntax.Internal                  (Name, DefName)
import qualified Term.Telescope                   as Tel
import           Term.Var
import           Term.Synonyms
import           Term.Subst
import           Term.TermM

-- Clauses
------------------------------------------------------------------------

-- | A 'ClauseBody' scopes a term over a number of variables.  The
-- lowest number refers to the rightmost variable in the patterns, the
-- highest to the leftmost.
type ClauseBody t v = t (Var (Named Int) v)

instantiateClauseBody
  :: (SubstVar v, Subst t) => ClauseBody t Void -> [t v] -> TermM (t v)
instantiateClauseBody body args0 = subst body $ \v -> case v of
  B (Bound.Name _ i) -> return $ ixArg i
  F v'               -> absurd v'
  where
    args = reverse args0

    ixArg n = if n >= length args
              then error "Definition.instantiateClauseBody: too many arguments"
              else args !! n


-- | One clause of a function definition.
data Clause t v = Clause [Pattern] (ClauseBody t v)
    deriving (Typeable)

instance (Eq1 t) => Eq1 (Clause t) where
  Clause pats1 body1 ==# Clause pats2 body2 = pats1 == pats2 && body1 ==# body2

instance Bound Clause where
  Clause pats body >>>= f = Clause pats $ fromScope (Scope body >>>= f)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Show)

patternBindings :: Pattern -> Int
patternBindings VarP          = 1
patternBindings (ConP _ pats) = patternsBindings pats

patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

-- Definition
------------------------------------------------------------------------

data Definition t v
    = Constant ConstantKind (Type t v)
    | DataCon Name (Tel.IdTel (Type t) v)
    -- ^ Data type name, telescope ranging over the parameters of the
    -- type constructor ending with the type of the constructor.
    | Projection Field Name (Tel.IdTel t v)
    -- ^ Field number, record type name, telescope ranging over the
    -- parameters of the type constructor ending with the type of the
    -- projection.
    | Function (Type t v) (Invertible t v)
    -- ^ Function type, clauses.
    deriving (Typeable)

instance Bound Definition where
  Constant kind t              >>>= f = Constant kind (t >>= f)
  DataCon tyCon type_          >>>= f = DataCon tyCon (type_ >>>= f)
  Projection field tyCon type_ >>>= f = Projection field tyCon (type_ >>>= f)
  Function type_ clauses       >>>= f = Function (type_ >>= f) (mapInvertible (>>>= f) clauses)

data ConstantKind
  = Postulate
  -- ^ Note that 'Postulates' might not be forever, since we add clauses
  -- when we encounter them.
  | Data [Name]
  -- ^ A data type, with constructors.
  | Record Name [(Name, Field)]
  -- ^ A record, with its constructors and projections.
  deriving (Eq, Show, Typeable)

-- | A function is invertible if each of its clauses is headed by a
-- different 'TermHead'.
data Invertible t v
  = NotInvertible [Clause t v]
  | Invertible [(TermHead, Clause t v)]
  -- ^ Each clause is paired with a 'TermHead' that doesn't happend
  -- anywhere else in the list.

-- deriving instance (IsTerm t) => Show (Closed (Invertible t))

-- | A 'TermHead' is an injective type- or data-former.
--
-- TODO Also include postulates when we have them to be explicit.
data TermHead = PiHead | DefHead DefName
    deriving (Eq, Show)

ignoreInvertible :: Invertible t v -> [Clause t v]
ignoreInvertible (NotInvertible clauses) = clauses
ignoreInvertible (Invertible injClauses) = map snd injClauses

mapInvertible :: (Clause t v -> Clause t' v')
              -> Invertible t v -> Invertible t' v'
mapInvertible f (NotInvertible clauses) = NotInvertible $ map f clauses
mapInvertible f (Invertible injClauses) = Invertible $ map (second f) injClauses

-- Pretty printing
------------------------------------------------------------------------

-- instance (IsTerm t) => PP.Pretty (Closed (Definition t)) where
--   pretty (Constant Postulate type_) =
--     prettyView type_
--   pretty (Constant (Data dataCons) type_) =
--     "data" <+> prettyView type_ <+> "where" $$
--     PP.nest 2 (PP.vcat (map PP.pretty dataCons))
--   pretty (Constant (Record dataCon fields) type_) =
--     "record" <+> prettyView type_ <+> "where" $$
--     PP.nest 2 ("constructor" <+> PP.pretty dataCon) $$
--     PP.nest 2 ("field" $$ PP.nest 2 (PP.vcat (map (PP.pretty . fst) fields)))
--   pretty (DataCon tyCon type_) =
--     "constructor" <+> PP.pretty tyCon $$ PP.nest 2 (prettyTele type_)
--   pretty (Projection _ tyCon type_) =
--     "projection" <+> PP.pretty tyCon $$ PP.nest 2 (prettyTele type_)
--   pretty (Function type_ clauses) =
--     prettyView type_ $$
--     PP.vcat (map PP.pretty (ignoreInvertible clauses))

-- prettyTele :: (IsVar v, IsTerm t) => Tel.IdTel t v -> PP.Doc
-- prettyTele (Tel.Empty (Tel.Id t)) =
--    prettyView t
-- prettyTele (Tel.Cons (n0, type0) tel0) =
--   "[" <+> PP.pretty n0 <+> ":" <+> prettyView type0 PP.<> go tel0
--   where
--     go :: (IsVar v, IsTerm t) => Tel.IdTel t v -> PP.Doc
--     go (Tel.Empty (Tel.Id t)) =
--       "]" <+> prettyView t
--     go (Tel.Cons (n, type_) tel) =
--       ";" <+> PP.pretty n <+> ":" <+> prettyView type_ <+> prettyTele tel

-- instance (IsTerm t) => Show (Closed (Definition t)) where
--   show = PP.render . PP.pretty

-- instance PP.Pretty ConstantKind where
--   pretty = PP.text . show

-- instance (IsTerm t) => PP.Pretty (Closed (Clause t)) where
--   pretty (Clause pats body) =
--     PP.pretty pats <+> "=" $$ PP.nest 2 (prettyView (substFromScope body))

-- instance (IsTerm t) => Show (Closed (Clause t)) where
--   show = PP.render . PP.pretty

-- instance PP.Pretty Pattern where
--   prettyPrec p e = case e of
--     VarP      -> PP.text "_"
--     ConP c es -> PP.prettyApp p (PP.pretty c) es
