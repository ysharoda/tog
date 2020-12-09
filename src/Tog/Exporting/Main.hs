module Tog.Exporting.Main where

import Tog.Exporting.Agda
import Tog.Raw
import Tog.Parse
import Tog.Deriving.Types
import Tog.Deriving.Lenses (name)
import Tog.Deriving.TUtils
import Tog.Deriving.Main
import Tog.Instrumentation (Mode(..)) 

import Tog.Exporting.AgdaPredStyle as PStyle 

import qualified Data.Map as Map
import Control.Lens ((^.))
import System.Directory
import System.IO (openFile, IOMode(WriteMode, AppendMode), hClose)
import Text.PrettyPrint.Leijen (putDoc, hPutDoc, text, vsep, linebreak)

export :: [Char] -> Mode -> FilePath -> IO ()
export dirName mode file =
  do curr_dir <- getCurrentDirectory
     createDirectoryIfMissing True $ curr_dir ++ "/" ++ dirName
     s <- readFile file
     case parseModule s of
       Right (Module _ _ (Lang_ defs)) -> 
          exportHelper dirName mode (processDefs defs) (theories defs)
       Left err -> putDoc err   
       _ -> error "wrong file structure" 

exportHelper :: FilePath -> Mode -> Module -> Map.Map Name_ GTheory -> IO ()
exportHelper dir mode (Module _ _ (Decl_ imods)) gtheories =
  do 
    mkPrelude dir prelude
    case mode of 
      Agda -> flatModules dir modules
      AgdaPredStyle -> predModules dir gtheories
      _ -> error "error: exporting to agda or tog?" 
    where (prelude,modules) = splitDecls $ filterDecls imods
exportHelper _ _ _ _ = error "wrong file structure"     

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

files :: [Char] -> Decl -> IO ()
files dir m@(Module_ (Module nm _ _)) = do 
   handle <- openFile (dir ++ "/" ++ nm^.name ++ ".agda") WriteMode
   hPutDoc handle $ printAgda (agdaModuleWithImports ("Prelude" : importNames) m)
   hClose handle 
files _ _ = error "something wrong"

-- ------------------- Utils ------------------------------------
splitDecls :: [Decl] -> ([Decl], [Decl])
splitDecls ds = ([d | d <- ds, not (isModule d)],
                 [m | m <- ds, isModule m])
    where isModule (Module_ _) = True
          isModule _ = False 

-- inputs: Module and a list of imports 
agdaModuleWithImports :: [String] -> Decl -> Decl 
agdaModuleWithImports  imprts (Module_ (Module nm prms (Decl_ defs))) =
  let importDecls = map (\str -> OpenImport (ImportNoArgs (mkQName str))) imprts 
  in Module_ (Module nm prms (Decl_ (importDecls ++ defs)))
agdaModuleWithImports _ _ = error "wrong file structure" 
