{-# OPTIONS_GHC -fno-warn-orphans #-}

module Tog.DerivingInsts where

import Tog.Raw.Abs
import qualified Data.Generics as Generics


deriving instance Generics.Data Name
deriving instance Generics.Typeable Name

deriving instance Generics.Data QName
deriving instance Generics.Typeable QName

deriving instance Generics.Data TypeSig
deriving instance Generics.Typeable TypeSig

deriving instance Generics.Data Params
deriving instance Generics.Typeable Params

deriving instance Generics.Data DataBody
deriving instance Generics.Typeable DataBody

deriving instance Generics.Data RecordBody
deriving instance Generics.Typeable RecordBody

deriving instance Generics.Data Fields
deriving instance Generics.Typeable Fields

deriving instance Generics.Data Constr
deriving instance Generics.Typeable Constr

deriving instance Generics.Data Telescope
deriving instance Generics.Typeable Telescope

deriving instance Generics.Data Binding
deriving instance Generics.Typeable Binding

deriving instance Generics.Data Expr
deriving instance Generics.Typeable Expr

deriving instance Generics.Data Arg
deriving instance Generics.Typeable Arg  

deriving instance Generics.Data FunDefBody
deriving instance Generics.Typeable FunDefBody

deriving instance Generics.Data HiddenName
deriving instance Generics.Typeable HiddenName

deriving instance Generics.Data Where
deriving instance Generics.Typeable Where

deriving instance Generics.Data Empty
deriving instance Generics.Typeable Empty

deriving instance Generics.Data Import
deriving instance Generics.Typeable Import

deriving instance Generics.Data Pattern
deriving instance Generics.Typeable Pattern

deriving instance Generics.Data Decl
deriving instance Generics.Typeable Decl

deriving instance Generics.Data Module
deriving instance Generics.Typeable Module

deriving instance Generics.Data DeclOrLE
deriving instance Generics.Typeable DeclOrLE

deriving instance Generics.Data Language
deriving instance Generics.Typeable Language 

deriving instance Generics.Data ModExpr
deriving instance Generics.Typeable ModExpr

deriving instance Generics.Data RenPair
deriving instance Generics.Typeable RenPair 

deriving instance Generics.Data Rens
deriving instance Generics.Typeable Rens

deriving instance Generics.Data ViewPair
deriving instance Generics.Typeable ViewPair 

