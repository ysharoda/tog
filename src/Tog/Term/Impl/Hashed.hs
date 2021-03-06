module Tog.Term.Impl.Hashed where

import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Term.Types
import           Tog.Term.Synonyms
import           Tog.Term.Impl.Common
import           Tog.Prelude


data Hashed = H Int (TermView Hashed)
  deriving (Typeable, Show)

instance Hashable Hashed where
  hashWithSalt s (H i _) = s `hashWithSalt` i

instance Eq Hashed where
  H i1 t1 == H i2 t2 = i1 == i2 && t1 == t2

instance Metas Hashed Hashed where
  metas = genericMetas

instance Nf Hashed Hashed where
  nf = genericNf

instance PrettyM Hashed Hashed where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst Hashed Hashed where
  safeApplySubst = genericSafeApplySubst

instance SynEq Hashed Hashed where
  synEq x y = return (x == y)

instance IsTerm Hashed where
  whnf t = do
    t' <- fromMaybe t <$> liftIO (lookupWhnfTerm t)
    blockedT <- genericWhnf t'
    -- TODO don't do a full traversal for this check
    t'' <- ignoreBlocking blockedT
    unless (t == t'') $ liftIO $ do
      -- TODO do not add both if we didn't get anything the with
      -- `lookupWhnfTerm'.
      insertWhnfTerm t t''
      insertWhnfTerm t' t''
    return blockedT

  view (H _ t) = return t
  unview tv = return $ H (hash tv) tv

  set = H (hash (Set :: Closed (TermView Hashed))) Set
  refl = H (hash (Refl :: Closed (TermView Hashed))) Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ runTermM sigEmpty genericTypeOfJ

-- Table

type TableKey = Hashed

{-# NOINLINE hashedTable #-}
hashedTable :: HT.CuckooHashTable TableKey Hashed
hashedTable = unsafePerformIO HT.new

lookupWhnfTerm :: Hashed -> IO (Maybe Hashed)
lookupWhnfTerm t0 = do
  HT.lookup hashedTable t0

insertWhnfTerm :: Hashed -> Hashed -> IO ()
insertWhnfTerm t1 t2 = HT.insert hashedTable t1 t2
