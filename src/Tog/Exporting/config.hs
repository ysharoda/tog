{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

{-
% configuration of a class:
c1 nm c2 params c3 type c4
  c5 constructor c6
  c7 fields c8
    c9 constr c10

% configuration of a structure: 
s1 nm s2 params s3 type s4
  s5 constructor s6
  s7 fields s8
    s9 constr s10

% configuration of a datatype:
d1 nm d2 params d3 type d4 
  d5 constr d6

% configuration of a function def:
f1 nm f2 binds f3 type f4
  f5 pattern f6 func_call f7

%configuration of a module
m1 nm m2 params m3 

m4
-}

module Tog.Exporting.Config where

import Tog.Instrumentation.Conf (Mode(..))

type ImportDecl = String

data Config = Config {
  target :: Mode,
  file_extension::String,
  equality :: String, 
  theory   :: String,
  open_theory :: Bool, 
  open_datatypes :: Bool,
  open_structures :: Bool,
  preprocessInd :: Bool ,
  preprocessFunc :: Bool,  
  constructors :: String, 
  fields :: String, 
  printConstructors :: Bool, 
  constr_oftype :: String,  
  bind_of_type :: String, 
  before_constr_binds :: String, 
  after_constr_binds :: String,
  before_ftype_binds :: String, -- bindings in the function types 
  after_ftype_binds :: String, 
  lambda :: String, 
  fun_sep :: String, 
  level0 :: String, 
  level1 :: String, 
  c1 :: String,
  c2 :: String,
  c3 :: String, 
  c4 :: Bool -> String, 
  c5 :: String, 
  c6 :: String, 
  c7 :: String, 
  c8 :: String, 
  c9 :: String, 
  c10 :: String, 
  s1 :: String, 
  s2 :: String, 
  s3 :: String,
  s4 :: Bool -> String, 
  s5 :: String, 
  s6 :: String, 
  s7 :: String, 
  s8 :: String, 
  s9 :: String, 
  s10 :: String, 
  d1 :: String, 
  d2 :: String, 
  d3 :: String, 
  d4 :: Bool -> String, 
  d5 :: String, 
  d6 :: String, 
  f1 :: String, 
  f2 :: String, 
  f3 :: String, 
  f4 :: String, 
  f5 :: String, 
  f6 :: String, 
  f7 :: String,
  constructors_as_functions:: Bool, 
  open_ :: String, 
  import_ :: String, 
  openimport :: String,
  import_before_module::Bool,
  m1 :: String, 
  m2 :: String, 
  m3 :: Bool -> String, 
  m4 :: String, 
  module_end_has_name :: Bool,
  prelude_includes :: Either FilePath ([ImportDecl],[String]),
  imports :: [String] }


agdaConfig :: Config
agdaConfig = Config {
  target = Agda,
  file_extension="agda",
  equality="≡",
  theory="record", 
  open_theory=True,
  open_datatypes=False,
  open_structures=False,
  preprocessInd=False,
  preprocessFunc=False, 
  constructors="",
  fields="field",
  printConstructors=False,
  constr_oftype=":", 
  bind_of_type=":",
  before_constr_binds="",
  after_constr_binds="→",
  before_ftype_binds="", -- bindings in the function types 
  after_ftype_binds="→",
  lambda="λ",
  fun_sep="→",
  level0="Set",
  level1="Set₁", 
  c1="record",
  c2="",
  c3=":",
  c4= (\_ -> "where"),
  c5="",
  c6="",
  c7="",
  c8="",
  c9="",
  c10="",
  s1="record",
  s2="",
  s3=":",
  s4= (\_ -> "where"),
  s5="",
  s6="",
  s7="",
  s8="",
  s9="",
  s10="",
  d1="data",
  d2="",
  d3=":",
  d4= (\_ -> "where"),
  d5="",
  d6="",
  f1="",
  f2=":",
  f3="",
  f4="",
  f5="fname",
  f6="=",
  f7="" ,
  constructors_as_functions=False,
  open_="open",
  import_="import",
  openimport="open import",
  import_before_module=False,
  m1="module",
  m2="",
  m3=(\_ -> "where"),
  m4="",
  module_end_has_name=False,
  -- To create Prelude, one can:
  -- - Use an existing file: Left FilePath
  -- - Create a prelude given a list of imports and a list of definitions to be exported from tog prelude. 
  prelude_includes=
    Right (["open import Agda.Builtin.Equality",
            "open import Agda.Builtin.Nat",
            "open import Data.Fin",
            "open import Data.Vec"]
          ,["Prod","Wrap","Stage","CodeRep","uncode","code","run",
                          "Choice","Comp","Staged","expr","const",
                          "stage0","stage1","stage2","codeLift1","codeLift2"]),
  imports=
    ["open import Prelude",
     "open import Agda.Builtin.Equality",
     "open import Agda.Builtin.Nat",
     "open import Data.Fin",
     "open import Data.Vec"]
} 

leanConfig = Config {
  target = Lean,
  file_extension="lean",
  equality="=",
  theory="class", 
  open_theory=True,
  open_datatypes=True,
  open_structures=False,
  preprocessInd=True,
  preprocessFunc=True,
  constructors="",
  fields="",
  printConstructors=False,
  constr_oftype=":",
  bind_of_type=":",
  before_constr_binds="∀",
  after_constr_binds=",",
  before_ftype_binds="", -- bindings in the function types 
  after_ftype_binds="",
  lambda="λ",
  fun_sep="→",
  level0="Type",
  level1="Type 1", 
  c1="class",
  c2="",
  c3=":",
  c4= (\empty -> if empty then "" else ":="),
  c5="",
  c6="",
  c7="",
  c8="",
  c9="(",
  c10=")",
  s1="structure",
  s2="",
  s3=":",
  s4= (\empty -> if empty then "" else ":="),
  s5="",
  s6="",
  s7="",
  s8="",
  s9="(",
  s10=")",
  d1="inductive",
  d2="",
  d3=":",
  d4= (\_ -> ""),
  d5="|",
  d6="",
  f1="def",
  f2="",
  f3=":",
  f4= "",
  f5="|",
  f6=":=",
  f7="",
  constructors_as_functions=False,
  open_="open",
  import_="import",
  openimport="",
  import_before_module=True,
  m1="section",
  m2="",
  m3= (\_ -> ""),
  m4="end",
  module_end_has_name=True,
  -- the list of definitions from tog prelude to be exported
  prelude_includes=Left "./Prelude.lean",
  imports=
     ["import init.data.nat.basic",
      "import init.data.fin.basic",
      "import data.vector",
      "import .Prelude",
      "open Staged",
      "open nat",
      "open fin", 
      "open vector"]
}
  
  
{-
import qualified Tog.Exporting.Lean.Config as LC
import qualified Tog.Exporting.Agda.Config as AC

target = readConf

equality = if (target /= "lean") then AC.equality else LC.equality
theory = if (target /= "lean") then AC.theory else LC.theory
open_theory = if (target == "lean") then AC.open_theory else LC.open_theory
open_datatypes = if (target /= "lean") then AC.open_datatypes else LC.open_datatypes
open_structures = if (target /= "lean") then AC.open_structures else LC.open_structures
preprocessInd = if (target /= "lean") then AC.preprocessInd else LC.preprocessInd
preprocessFunc = if (target /= "lean") then AC.preprocessFunc else LC.preprocessFunc

constructors = if (target /= "lean") then AC.constructors else LC.constructors
fields = if (target /= "lean") then AC.fields else LC.fields
printConstructors = if (target /= "lean") then AC.printConstructors else LC.printConstructors
constr_oftype = if (target /= "lean") then AC.constr_oftype else LC.constr_oftype
bind_of_type = if (target /= "lean") then AC.bind_of_type else LC.bind_of_type
before_constr_binds = if (target /= "lean") then AC.before_constr_binds else LC.before_constr_binds
after_constr_binds = if (target /= "lean") then AC.after_constr_binds else LC.after_constr_binds
before_ftype_binds = if (target /= "lean") then AC.before_ftype_binds else LC.before_ftype_binds
after_ftype_binds = if (target /= "lean") then AC.after_ftype_binds else LC.after_ftype_binds
lambda = if (target /= "lean") then AC.lambda else LC.lambda
fun_sep = if (target /= "lean") then AC.fun_sep else LC.fun_sep
level0 = if (target /= "lean") then AC.level0 else LC.level0
level1 = if (target /= "lean") then AC.level1 else LC.level1

c1  = if (target /= "lean") then AC.c1  else LC.c1
c2  = if (target /= "lean") then AC.c2  else LC.c2
c3  = if (target /= "lean") then AC.c3  else LC.c3
c4  = if (target /= "lean") then AC.c4  else LC.c4
c5  = if (target /= "lean") then AC.c5  else LC.c5
c6  = if (target /= "lean") then AC.c6  else LC.c6
c7  = if (target /= "lean") then AC.c7  else LC.c7
c8  = if (target /= "lean") then AC.c8  else LC.c8
c9  = if (target /= "lean") then AC.c9  else LC.c9
c10 = if (target /= "lean") then AC.c10 else LC.c10

s1  = if (target /= "lean") then AC.s1  else LC.s1
s2  = if (target /= "lean") then AC.s2  else LC.s2
s3  = if (target /= "lean") then AC.s3  else LC.s3
s4  = if (target /= "lean") then AC.s4  else LC.s4
s5  = if (target /= "lean") then AC.s5  else LC.s5
s6  = if (target /= "lean") then AC.s6  else LC.s6
s7  = if (target /= "lean") then AC.s7  else LC.s7
s8  = if (target /= "lean") then AC.s8  else LC.s8
s9  = if (target /= "lean") then AC.s9  else LC.s9
s10 = if (target /= "lean") then AC.s10 else LC.s10

d1 = if (target /= "lean") then AC.d1 else LC.d1
d2 = if (target /= "lean") then AC.d2 else LC.d2
d3 = if (target /= "lean") then AC.d3 else LC.d3
d4 = if (target /= "lean") then AC.d4 else LC.d4
d5 = if (target /= "lean") then AC.d5 else LC.d5
d6 = if (target /= "lean") then AC.d6 else LC.d6

f1 = if (target /= "lean") then AC.f1 else LC.f1
f2 = if (target /= "lean") then AC.f2 else LC.f2
f3 = if (target /= "lean") then AC.f3 else LC.f3
f4 = if (target /= "lean") then AC.f4 else LC.f4
f5 = if (target /= "lean") then AC.f5 else LC.f5
f6 = if (target /= "lean") then AC.f6 else LC.f6
f7 = if (target /= "lean") then AC.f7 else LC.f7

open_ = if (target /= "lean") then AC.open_ else LC.open_
import_ = if (target /= "lean") then AC.import_ else LC.import_
openimport = if (target /= "lean") then AC.openimport else LC.openimport
m1 = if (target /= "lean") then AC.m1 else LC.m1
m2 = if (target /= "lean") then AC.m2 else LC.m2
m3 = if (target /= "lean") then AC.m3 else LC.m3
m4 = if (target /= "lean") then AC.m4 else LC.m4
module_end_has_name = if (target /= "lean") then AC.module_end_has_name else LC.module_end_has_name

prelude_includes = if (target /= "lean") then AC.prelude_includes else LC.prelude_includes

imports = if (target /= "lean") then AC.imports else LC.imports
-}

