module Interpret.Exporting.Agda.Preprocess where

import Tog.Raw.Abs
import Interpret.Utils.TUtils (getArgName)
import Interpret.Flattener.Types (gmap)
import Interpret.Exporting.Utils (preprocessSig, implPattern, implArg) 

import Data.List.Split (splitOn)

-- adding open declarations to the theory 
preprocessDecls :: [Decl] -> [Decl]
preprocessDecls [] = [] 
preprocessDecls ((FunDef nm ps body):ds) =
  (FunDef nm (preprocessPatterns ps) (preprocessFunBody body)) : preprocessDecls ds
preprocessDecls ((TypeSig sig):ds) = (TypeSig $ preprocessSig sig) : preprocessDecls ds
preprocessDecls (d:ds) = d : preprocessDecls ds

preprocessPatterns :: [Pattern] -> [Pattern]
preprocessPatterns ps = dropWhile implPattern ps

preprocessFunBody :: FunDefBody -> FunDefBody
preprocessFunBody body = gmap process body
  where process (App (nm:as)) =
         App $ nm : dropWhile implArg as
        process e = e

callFunc :: Expr -> Expr
callFunc a@(App [nm,_,a1,a2]) =
  if (getArgName nm == "lookup") then App [nm,a2,a1] else a
callFunc e = e

replace :: String -> String
replace nm =
  let pieces = splitOn "_" nm
      cond = \x → if (x == "0" || x == "1") then x ++ "ᵢ" else x
      postProcess lst = (head lst) : (map ("_"++) $ tail lst)
  in concat $ postProcess $ map cond pieces  
