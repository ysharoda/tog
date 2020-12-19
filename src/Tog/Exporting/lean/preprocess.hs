
module Tog.Exporting.Lean.Preprocess where

import Tog.Raw.Abs
import Tog.Deriving.Lenses (name)
import Tog.Deriving.TUtils (getArgName, mkArg)
import Tog.Deriving.Types (gmap)

import Tog.Exporting.Config

import Control.Lens ((^.))

-- drops the bindings from the pattern matching list and the function call list 
explicitArgsNum :: [Binding] -> Int
explicitArgsNum [] = 0 
explicitArgsNum ((Bind as _):bs) = length as + explicitArgsNum bs
explicitArgsNum ((HBind _ _):bs) = explicitArgsNum bs

preprocessPatterns :: [Binding] -> [Pattern] -> [Pattern]
preprocessPatterns binds patterns =
  let argsNum = explicitArgsNum binds 
  in drop argsNum patterns

preprocessFunBody :: Name -> [Binding] -> FunDefBody -> FunDefBody 
preprocessFunBody funcNm binds body = gmap process body
   where
     argsNum = explicitArgsNum binds
     process (App (nm:as)) = App $ nm : if (getArgName nm) == funcNm^.name then drop argsNum as else as
     process e = e
    
preprocessDecls :: [Decl] -> [Decl]
preprocessDecls ((TypeSig sig):decls) =
  (TypeSig sig) : (preprocessDecls $ map (replaceDef sig) decls)
  where
    replaceDef (Sig tnm (Pi (Tel binds) _)) f@(FunDef fnm ps body) =
     if (tnm^.name == fnm^.name)
     then FunDef fnm (preprocessPatterns binds ps) (preprocessFunBody fnm binds body) else f
    replaceDef _ f = f 
preprocessDecls ((Data nm ps body):decls) = -- removing the params when referring to the inductive type 
  (Data nm ps (gmap helper body)) : preprocessDecls decls 
  where 
   helper e@(App (a1:_)) = if (getArgName a1 == nm^.name) then App [a1] else e
   helper e = e
preprocessDecls (d:decls) = d : preprocessDecls decls
preprocessDecls [] = []

{-
-- in case only class header changes from the record 
-- won't scale if the syntax of the class body is very different. 
recordAsClass :: Decl -> Doc
recordAsClass (Record nm ps body) =
  text c1 <+> printLean nm <+> text c2 <+> printLean ps <+> text c3 <+> printLean body
recordAsClass _ = error "not a record" 
-}

replace :: String -> String
replace nm =
  if (nm == "Set") then (level0 leanConfig) 
  else if (nm == "expr") then "expr'"
  else if (nm == "Nat") then "ℕ"
  else if (nm == "Vec") then "vector"
  else if (nm == "Fin") then "fin"
  else if (elem '-' nm) then map (\x -> if x =='-' then '_' else x) nm 
  else nm

callFunc :: Expr -> Expr
callFunc a@(App [nm,_,a2,a3]) =
  if (getArgName nm == "lookup") then App [mkArg "nth",a3,a2] else a
callFunc e = e
