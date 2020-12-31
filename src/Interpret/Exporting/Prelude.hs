module Interpret.Exporting.Prelude where 

import Tog.Raw.Abs
import Interpret.Utils.TUtils (mkName) 
import Interpret.Exporting.Config
import Interpret.Exporting.Utils (mkImports, declName)
import Interpret.Exporting.LeanPrelude

import Text.PrettyPrint.Leijen (Doc, hPutDoc)
import System.Directory
import System.IO (openFile, IOMode(WriteMode), hClose)

writePrelude :: Config -> Either FilePath Doc -> FilePath -> IO ()
writePrelude conf (Left prld) dst =
  let ext = file_extension conf
  in if ext == "lean" then writePrelude conf (Right leanPrelude) dst 
     else copyFile prld $ dst ++ "/" ++ "Prelude." ++ ext 
writePrelude conf (Right doc) dst = do
  handle <- openFile (dst ++ "/" ++ "Prelude."++ file_extension conf) WriteMode
  hPutDoc handle $ doc
  hClose handle

-- input: tog prelude decls   
prelude ::  Config -> [Decl] -> Either FilePath Decl
prelude conf decls =
  case (prelude_includes conf) of -- reading the config file
    Left file -> Left file
    Right (imprts,toExport) -> Right $ 
      Module_ $ Module (mkName "Prelude") NoParams $ 
                 Decl_ $ mkImports conf imprts ++ isIncluded toExport decls 
        
isIncluded :: [String] -> [Decl] -> [Decl]
isIncluded toExport decls = filter (\x -> elem (declName x) toExport) decls  
