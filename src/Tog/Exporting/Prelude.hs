module Tog.Exporting.Prelude where 

import Tog.Raw.Abs
import Tog.Deriving.TUtils (mkName, getName) 
import Tog.Deriving.Lenses (name)
import Tog.Exporting.Config
import Tog.Exporting.Utils (mkImports)
import Tog.Exporting.LeanPrelude

import Control.Lens ((^.))
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
isIncluded toExport decls =
  let declName d = case d of
        TypeSig (Sig n _) -> n^.name 
        FunDef n _ _ -> n^.name
        Data n _ _ -> n^.name
        Record n _ _ -> n^.name
        Open qn -> getName qn
        OpenImport (ImportNoArgs qn) -> getName qn
        OpenImport (ImportArgs qn _) -> getName qn
        Import  (ImportNoArgs qn) -> getName qn
        Import (ImportArgs qn _)  -> getName qn
        Postulate _ -> ""
        Module_ (Module n _ _ ) -> n^.name 
  in filter (\x -> elem (declName x) toExport) decls  
