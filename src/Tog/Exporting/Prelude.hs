module Tog.Exporting.Prelude where 

import Tog.Raw.Abs
import Tog.Deriving.TUtils (mkName, getName) 
import Tog.Deriving.Lenses (name)
import Tog.Exporting.Config
import Tog.Exporting.Utils (mkImports) 

import Control.Lens ((^.))
import Text.PrettyPrint.Leijen (Doc, hPutDoc)
import System.Directory
import System.IO (openFile, IOMode(WriteMode), hClose)

writePrelude :: Either FilePath Doc -> FilePath -> IO ()
writePrelude (Left prld) dst = copyFile prld $ dst ++ "/" ++ "Prelude.agda" 
writePrelude (Right doc) dst = do
  handle <- openFile (dst ++ "/" ++ "Prelude.agda") WriteMode
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
