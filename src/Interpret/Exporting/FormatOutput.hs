module Interpret.Exporting.FormatOutput where 
-- the input is a [Decls] and this file formats it into separate files 

import Tog.Raw.Abs 

import Interpret.Utils.Lenses (name)
import Interpret.Exporting.Export
import Interpret.Exporting.Config 
import Interpret.Exporting.Utils
import Interpret.Exporting.Prelude (writePrelude, prelude) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen (hPutDoc)
import System.IO (openFile, IOMode(WriteMode), hClose)

moduleWithImports :: Config -> Module -> Module 
moduleWithImports conf (Module n p (Decl_ decls)) =
  Module n p (Decl_ $ (mkImports conf $ imports conf) ++ decls)
moduleWithImports _ _ = error "wrong structure of modules: expected a flat module" 
  
files :: FilePath -> Config -> Decl -> IO ()
files dir conf (Module_ m@(Module nm _ _)) = do
   handle <- openFile (dir ++ "/" ++ nm^.name ++ "." ++ file_extension conf) WriteMode
   hPutDoc handle $ export conf (openTheory conf $ moduleWithImports conf m)
   hClose handle 
files _ _ _ = error "something wrong"
  
print :: Config -> FilePath -> Module -> IO ()
print conf dir (Module _ _ (Decl_ decls)) = 
 let (prld,modules) = splitDecls decls
     prludeModule = case prelude conf prld of
       Right m -> Right (export conf m)
       Left f -> Left f  
  in do writePrelude conf prludeModule dir 
        mapM_ (files dir conf) modules  
print _ _ _ = error "wrong structure of modules: expected a flat module" 
