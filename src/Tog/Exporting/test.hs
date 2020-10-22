module Test where

import Tog.Deriving.Main  (processDefs, defsToModule)
import Tog.Exporting.Agda
import Tog.Raw                  
import Tog.Parse
import Tog.Deriving.Lenses (name)
import Tog.Deriving.TUtils 

import Control.Lens ((^.))
import System.IO (openFile, IOMode(WriteMode, AppendMode), hClose)
import Text.PrettyPrint.Leijen (putDoc, hPutDoc, text, vsep, linebreak) 

test :: [Char] -> FilePath -> IO ()
test dirName file = do
 s <- readFile file
 case parseModule s of
   Left err -> putDoc err
   Right (Module _ _ (Lang_ defs)) -> 
    case processDefs defs of
      (Module _ _ (Decl_ imods)) -> do 
        mkPrelude dirName prelude
        internalModule dirName modules 
        where (prelude,modules) = splitDecls $ filterDecls imods
      _ -> error "wrong file structure" 
{-
test2 :: [Char] -> FilePath -> IO ()
test2 dirName file = do
 s <- readFile file
 case parseModule s of
   Left err -> putDoc err
   Right (Module _ _ (Lang_ defs)) -> 
    case defsToModule defs of
      (Module _ _ (Decl_ imods)) -> do 
        internalModule dirName allModules
        where (prelude,modules) = splitDecls $ filterDecls imods
              allModules = (preludeModule prelude) :
                           (map (agdaModuleWithImports ("Prelude" : importNames)) modules) 
      _ -> error "wrong file structure" 
-}
-- prints Prelude to a file 
mkPrelude :: PrintAgda a => [Char] -> [a] -> IO ()        
mkPrelude dirName ds = do
  handle <- openFile (dirName ++ "/" ++ "Prelude.agda") AppendMode
  hPutDoc handle $ text "module Prelude where\n" <> (vsep imports) <> linebreak
  hPutDoc handle $ vsep $ map printAgda ds
  hClose handle

-- creates the Prelude module
preludeModule :: [Decl] -> Decl 
preludeModule prelude =
  let importDecls i = OpenImport (ImportNoArgs (mkQName i))
  in Module_ (Module (mkName "Prelude") NoParams
                 (Decl_ $ (map importDecls importNames) ++ prelude))
  
internalModule :: Foldable t => [Char] -> t Decl -> IO ()
internalModule dirName modules =
  mapM_ (internalModuleHelper dirName) modules 

internalModuleHelper :: [Char] -> Decl -> IO ()
internalModuleHelper dirName m@(Module_ (Module nm _ _)) = do 
   handle <- openFile (dirName ++ "/" ++ nm^.name ++ ".agda") WriteMode
   hPutDoc handle $ printAgda (agdaModuleWithImports ("Prelude" : importNames) m)
   hClose handle 
internalModuleHelper _ _ = error "something wrong"

-- inputs: Module and a list of imports 
agdaModuleWithImports :: [String] -> Decl -> Decl 
agdaModuleWithImports  imprts (Module_ (Module nm prms (Decl_ defs))) =
  let importDecls = map (\str -> OpenImport (ImportNoArgs (mkQName str))) imprts 
  in Module_ (Module nm prms (Decl_ (importDecls ++ defs)))
agdaModuleWithImports _ _ = error "wrong file structure" 

splitDecls :: [Decl] -> ([Decl], [Decl])
splitDecls ds = ([d | d <- ds, not (isModule d)],
                 [m | m <- ds, isModule m])
    where isModule (Module_ _) = True
          isModule _ = False 
