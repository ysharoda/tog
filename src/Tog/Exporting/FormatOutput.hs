module Tog.Exporting.FormatOutput where 
-- the input is a [Decls] and this file formats it into separate files 

import Tog.Raw.Abs 

import Tog.Deriving.Lenses (name)
import Tog.Exporting.Export
import Tog.Exporting.Config 
import Tog.Exporting.Utils
import Tog.Exporting.Prelude (writePrelude, prelude) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen (hPutDoc)
import System.IO (openFile, IOMode(WriteMode), hClose)

preprocess :: Config -> Module -> Module 
preprocess conf (Module n p (Decl_ decls)) =
  Module n p (Decl_ $ (mkImports conf $ imports conf) ++ (preprocessDecls conf decls))
    
--  Module n p (Decl_ $ map (moduleWithImports conf) $ preprocessDecls conf decls)
preprocess _ _ = error "wrong structure of modules: expected a flat module" 
  
files :: FilePath -> Config -> Decl -> IO ()
files dir conf (Module_ m@(Module nm _ _)) = do 
   handle <- openFile (dir ++ "/" ++ nm^.name ++ ".agda") WriteMode
   hPutDoc handle $ export conf (preprocess conf m)
   hClose handle 
files _ _ _ = error "something wrong"
  
print :: Config -> FilePath -> Module -> IO ()
print conf dir (Module _ _ (Decl_ decls)) = 
 let (prld,modules) = splitDecls decls
     prludeModule = case prelude conf prld of
       Right m -> Right (export conf m)
       Left f -> Left f  
--     theories = map (\(Module_ x) -> Module_ (preprocess conf x)) modules
  in do writePrelude prludeModule dir 
        mapM_ (files dir conf) modules  
print _ _ _ = error "wrong structure of modules: expected a flat module" 

{-
let checkDecl d = case d of
        Module_ m -> Module_ $ moduleWithImports conf m
        x -> x 
  in Module n p $ Decl_ (
-} 
