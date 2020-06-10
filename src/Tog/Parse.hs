module Tog.Parse (parseModule, parseExpr,parseDecl) where

import           Tog.Raw
import           Tog.Raw.ErrM                     (Err(Bad, Ok))
import           Tog.Raw.Layout                   (resolveLayout)
import           Tog.Raw.Par                      (myLexer, pModule, pExpr, pDecl)
import qualified Tog.PrettyPrint                  as PP

parseModule :: String -> Either PP.Doc Module
parseModule s =
  case pModule (resolveLayout True (myLexer s)) of
    Bad err -> Left $ PP.text err
    Ok p    -> Right p

parseExpr :: String -> Either PP.Doc Expr
parseExpr s =
  case pExpr (resolveLayout False (myLexer s)) of
    Bad err -> Left $ PP.text err
    Ok p    -> Right p

parseDecl :: String -> Either PP.Doc Decl
parseDecl decl =
  case pDecl (resolveLayout False (myLexer decl)) of
    Bad err -> Left $ PP.text err
    Ok p    -> Right p 

