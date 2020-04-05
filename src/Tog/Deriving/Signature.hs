module Tog.Deriving.Signature where

import Data.Generics as Generics(Data,Typeable)

import Tog.Raw.Abs
import Tog.Deriving.EqTheory 
import Tog.Deriving.TUtils
import Tog.Deriving.Types    (gmap, Name_)

data Signature = Signature {
  sigName :: Name_ ,
  sigSort :: Constr,
  sigFuncType :: [Constr],
  sigWaist :: Int } 
  deriving (Show,Eq,Generics.Data,Generics.Typeable)

signature_ :: EqTheory -> Signature
signature_ thry =
  let ren (Name (_,x)) = if (x == "Set") then mkName x else mkName $ x++"S"
      renThry = gmap ren thry 
  in Signature (thryName renThry++"Sig") (sort renThry) (funcTypes renThry) (waist renThry) 

params :: Signature -> Params
params sig = if (sigWaist sig == 0) then NoParams
  else let pars = take (sigWaist sig) (sigSort sig : sigFuncType sig)
       in ParamDecl $ map fldsToBinding pars 

fldsToBinding :: Constr -> Binding
fldsToBinding (Constr nm typ) =
  Bind [Arg $ createId $ name_ nm] typ 

sigToDecl :: Signature -> Decl
sigToDecl sig@(Signature nm srt fts wst) =
  Record (mkName nm) (params sig)
    (RecordDeclDef (mkName "Set") (mkName $ nm ++ "SigC")
      (let flds = drop wst (srt : fts)
       in if flds == [] then NoFields else Fields flds)) 
