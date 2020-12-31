
module Interpret.Exporting.Lean.Preprocess where

import Tog.Raw.Abs
import Interpret.Utils.Lenses (name)
import Interpret.Utils.TUtils (getArgName, mkArg)
import Interpret.Flattener.Types (gmap)

import Interpret.Exporting.Config
import Interpret.Exporting.Utils (preprocessSig, implPattern, implArg) 

import Control.Lens ((^.))
import Data.List (intersperse)
import Data.List.Split (splitOn) 

-- drops the bindings from the pattern matching list and the function call list 
explicitArgsNum :: [Binding] -> Int
explicitArgsNum [] = 0 
explicitArgsNum ((Bind as _):bs) = length as + explicitArgsNum bs
explicitArgsNum ((HBind _ _):bs) = explicitArgsNum bs

preprocessPatterns :: [Binding] -> [Pattern] -> [Pattern]
preprocessPatterns binds patterns =
  let argsNum = explicitArgsNum binds 
  in  drop argsNum $ dropWhile implPattern patterns

preprocessFunBody :: Name -> [Binding] -> FunDefBody -> FunDefBody 
preprocessFunBody funcNm binds body = gmap process body
   where
     argsNum = explicitArgsNum binds
     process (App (nm:as)) =
       App $ nm : if (getArgName nm) == funcNm^.name then drop argsNum $ dropWhile implArg as else as
     process e = e
     
preprocessDecls :: [Decl] -> [Decl]
preprocessDecls ((TypeSig sig):decls) =
  (TypeSig $ preprocessSig sig) : (preprocessDecls $ map (replaceDef sig) decls)
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

replace :: String -> String
replace nm =
  if (nm == "Set") then (level0 leanConfig) 
  else if (nm == "expr") then "expr'"
  else if (nm == "Nat") then "ℕ"
  else if (nm == "Vec") then "vector"
  else if (nm == "Fin") then "fin"
  else replaceNumber $ replaceSymbol $ replaceDash nm
  where
    checkNumber x = if x == '0' then "zero" else if x == '1' then "one" else [x]
    checkSymbol x =
      if x == '+' then "plus"
      else if x == '*' then "times"
      else if x == '>' then "linv"
      else if x == '<' then "rinv"
      else if x == '|' then ""
      else [x]
    replaceDash str = map (\x -> if x == '-' then '_' else x) str
    replaceNumber str =
     let helper x = if (length x == 1) then checkNumber (head x) else x 
     in if (str == []) then [] 
        else replaceFirst $  
             concat $ (intersperse "_") $ map helper $ splitOn "_" str
    replaceFirst [] = [] 
    replaceFirst (x:xs) = (checkNumber x) ++ xs
    replaceSymbol str = concat $ map checkSymbol str 

callFunc :: Expr -> Expr
callFunc a@(App [nm,_,a1,a2]) =
  if (getArgName nm == "lookup") then App [mkArg "nth",a2,a1] else a
callFunc e = e
