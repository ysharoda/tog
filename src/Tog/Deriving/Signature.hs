module Tog.Deriving.Signature 
  ( Signature
  , signature_
  , sigToDecl
  ) where

import Data.Generics as Generics(Data,Typeable)

import Tog.Raw.Abs
import qualified Tog.Deriving.EqTheory as Eq
import Tog.Deriving.TUtils
import Tog.Deriving.Types    (gmap, Name_)

data Signature = Signature {
  name :: Name_ ,
  sort :: Constr,
  funcType :: [Constr],
  waist :: Int } 
  deriving (Generics.Data,Generics.Typeable)

ren :: Name -> Name
ren n = mkName $ if (nam == "Set") then nam else nam ++ "S"
  where nam = name_ n

signature_ :: Eq.EqTheory -> Signature
signature_ thry = let t = gmap ren thry in 
  Signature (Eq.thryName t ++ "Sig") (Eq.sort t) (Eq.funcTypes t) (Eq.waist t) 

params :: Signature -> Params
params sig = if (waist sig == 0) then NoParams
  else let pars = take (waist sig) (sort sig : funcType sig)
       in ParamDecl $ map fldsToBinding pars 

fldsToBinding :: Constr -> Binding
fldsToBinding (Constr nm typ) = Bind [mkArg $ name_ nm] typ 

sigToDecl :: Signature -> Decl
sigToDecl sig@(Signature nm srt fts wst) =
  Record (mkName $ name sig) (params sig)
    (RecordDeclDef setType (mkName $ nm ++ "SigC")
      (mkField $ drop wst (srt : fts)))
