 module Interpret.Exporting.Main where

import Tog.Raw.Abs
import Tog.Parse
import Interpret.Flattener.Types
import Interpret.Deriving.Main
import Tog.Instrumentation (TargetLanguage(..)) 
import Tog.Print

import Interpret.Exporting.FormatOutput as Format
import Interpret.Exporting.AgdaPredStyle as PStyle
import Interpret.Exporting.Config 

import qualified Data.Map as Map
import System.Directory
import Text.PrettyPrint.Leijen (putDoc, hPutDoc)
import System.IO (openFile, IOMode(WriteMode), hClose)
  
main :: [Char] -> TargetLanguage -> FilePath -> IO ()
main dirName mode file = do 
  s <- readFile file
  case parseModule s of
    Right (Module _ _ (Lang_ defs)) -> do 
      case mode of
        Tog -> writeTogFile dirName (processDefs defs)         
        _   -> do 
            curr_dir <- getCurrentDirectory
            createDirectoryIfMissing True $ curr_dir ++ "/" ++ dirName 
            exportHelper dirName mode (processDefs defs) (theories defs)
    Left err -> putDoc err   
    _ -> error "wrong file structure" 

writeTogFile :: FilePath -> Module -> IO ()
writeTogFile file modules =
  do 
    handle <- openFile file WriteMode
    hPutDoc handle $ prettyprint modules  
    hClose handle

exportHelper :: FilePath -> TargetLanguage -> Module -> Map.Map Name_ GTheory -> IO ()
exportHelper dir mode modules@(Module n p _) gtheories =
  do case mode of 
      Agda -> Format.print (config mode) dir modules
      Lean -> Format.print (config mode) dir modules
      AgdaPredStyle -> Format.print (config mode) dir predModules
       where predModules = Module n p (Decl_ $ PStyle.makeInnerModules gtheories)
      _ -> error "the target language is not supported."       
      
config :: TargetLanguage -> Config
config Lean = leanConfig
config _ = agdaConfig 
