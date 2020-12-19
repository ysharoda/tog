module Tog.Exporting.Agda.Preprocess where

import Tog.Raw.Abs
import Tog.Deriving.TUtils (getArgName)

import Data.List.Split (splitOn)

-- adding open declarations to the theory 
preprocessDecls :: [Decl] -> [Decl]
preprocessDecls ds = ds
{-
preprocessDecls ds = map helper ds
  where
    helper (Module_ (Module nm params (Decl_ decls))) =
      let
       firstPart = takeWhile (not . hasModuleName) decls ++ filter hasModuleName decls
       rest = decls \\ firstPart
       hasModuleName (Record rnm _ _) = rnm == nm
       hasModuleName _ = False
      in 
       Module_ $ Module nm params (Decl_ $ firstPart ++ [Open $ NotQual nm] ++ rest)
    helper m = m 
-}
callFunc :: Expr -> Expr
callFunc a@(App [nm,_,a2,a3]) =
  if (getArgName nm == "lookup") then App [nm,a3,a2] else a
callFunc e = e

replace :: String -> String
replace nm =
  let pieces = splitOn "_" nm
      cond = \x → if (x == "0" || x == "1") then x ++ "ᵢ" else x
      postProcess lst = (head lst) : (map ("_"++) $ tail lst)
  in concat $ postProcess $ map cond pieces  
