module Tog.Deriving.Signature 
  ( Signature
  , signature_
  , sigToDecl
  ) where

import Data.Generics as Generics(Data,Typeable)
import           Control.Lens ((^.))

import Tog.Raw.Abs
import qualified Tog.Deriving.EqTheory as Eq
import Tog.Deriving.TUtils
import Tog.Deriving.Types    (gmap, Name_)
import Tog.Deriving.Lenses   (name)

data Signature = Signature {
  sname :: Name_ ,
  sort :: Constr,
  funcType :: [Constr],
  waist :: Int } 
  deriving (Generics.Data,Generics.Typeable)

ren :: Name -> Name
ren n = mkName $ if (nam == "Set") then nam else nam ++ "S"
  where nam = n^.name

signature_ :: Eq.EqTheory -> Signature
signature_ thry = let t = gmap ren thry in 
  Signature (Eq.thryName t ++ "Sig") (Eq.sort t) (Eq.funcTypes t) (Eq.waist t) 

params :: Signature -> Params
params sig = if (waist sig == 0) then NoParams
  else let pars = take (waist sig) (sort sig : funcType sig)
       in ParamDecl $ map fldsToBinding pars 

sigToDecl :: Signature -> Decl
sigToDecl sig@(Signature nm srt fts wst) =
  Record (mkName $ sname sig) (params sig)
    (RecordDeclDef setType (mkName $ nm ++ "SigC")
      (mkField $ drop wst (srt : fts)))
