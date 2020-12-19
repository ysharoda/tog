module Tog.Exporting.Main where

import Tog.Raw.Abs
import Tog.Parse
import Tog.Deriving.Types
import Tog.Deriving.Main
import Tog.Instrumentation (Mode(..)) 

import Tog.Exporting.FormatOutput as Format
import Tog.Exporting.AgdaPredStyle as PStyle
import Tog.Exporting.Config 

import qualified Data.Map as Map
import System.Directory
import Text.PrettyPrint.Leijen (putDoc) 
  
main :: [Char] -> Mode -> FilePath -> IO ()
main dirName mode file =
  do curr_dir <- getCurrentDirectory
     createDirectoryIfMissing True $ curr_dir ++ "/" ++ dirName
     s <- readFile file
     case parseModule s of
       Right (Module _ _ (Lang_ defs)) -> 
          exportHelper dirName mode (processDefs defs) (theories defs)
       Left err -> putDoc err   
       _ -> error "wrong file structure" 

exportHelper :: FilePath -> Mode -> Module -> Map.Map Name_ GTheory -> IO ()
exportHelper dir mode modules@(Module n p _) gtheories =
  do case mode of 
      Agda -> Format.print (config mode) dir modules
      Lean -> Format.print (config mode) dir modules
      AgdaPredStyle -> Format.print (config mode) dir predModules
       where predModules = Module n p (Decl_ $ PStyle.makeInnerModules gtheories)
      _ -> error "error: exporting to agda, lean or tog?"


config :: Mode -> Config
config Lean = leanConfig
config _ = agdaConfig 
