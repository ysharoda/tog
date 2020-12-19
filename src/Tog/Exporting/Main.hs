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
{-
-- -------------------- Prelude File --------------------
-- prints Prelude to a file 
mkPrelude :: PrintAgda a => [Char] -> [a] -> IO ()        
mkPrelude dir ds = do
  handle <- openFile (dir ++ "/" ++ "Prelude.agda") AppendMode
  hPutDoc handle $ text "module Prelude where\n" <> (vsep imports) <> linebreak
  hPutDoc handle $ vsep $ map printAgda ds
  hClose handle

-- creates the Prelude module
preludeModule :: [Decl] -> Decl 
preludeModule prelude =
  let importDecls i = OpenImport (ImportNoArgs (mkQName i))
  in Module_ (Module (mkName "Prelude") NoParams
                 (Decl_ $ (map importDecls importNames) ++ prelude))     

-- ----------- Writing the modules to files --------------

-- AgdaFlatTheories.agdaModuleWithImports :: [String] -> Decl -> Decl
-- AgdaPredStyle.agdaModuleWithImports :: [String] -> Name_ -> GTheory -> Decl 

flatModules :: Foldable t => [Char] -> t Decl -> IO ()
flatModules dir modules =
  mapM_ (files dir) modules

predModules :: FilePath -> Map.Map Name_ GTheory -> IO ()
predModules dir thrs =
  mapM_ (files dir) $ PStyle.makeInnerModules thrs  


-- ------------------- Utils ------------------------------------

-}
