{-# LANGUAGE OverloadedStrings #-}
module Interpret.Main (main) where

import           Prelude                          hiding (interact)

import           Options.Applicative
import           Options.Applicative.Types
import           System.Exit                      (exitFailure)
import           Data.List.Split                  (splitOn)

import           Tog.Instrumentation
import           Tog.PrettyPrint                  ((<+>), ($$))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Prelude
import           Tog.Term
import           Tog.CheckFile
import           Tog.Parse
import           Tog.ScopeCheck
import qualified Interpret.Exporting.Main as Export

-- import System.TimeIt 

parseTypeCheckConf :: Parser Conf
parseTypeCheckConf = Conf
  <$> strOption
      ( long "termType" <> short 't' <> value "GR" <>
        help "Available types: S (Simple), GR (GraphReduce), GRS (GraphReduceSub), GRU (GraphReduceUnpack), H (Hashed)."
      )
  <*> strOption
      ( long "solver" <> value "S" <>
        help "Available solvers: S (Simple)."
      )
  <*> debugLabelsOption
      ( long "debug" <> short 'd' <> value mempty <>
        help "Select debug labels to print. -d '' will print all the debug messages."
      )
  <*> switch
      ( long "stackTrace" <> short 's' <>
        help "Print a stack trace on error."
      )
  <*> switch
      (long "quiet" <> short 'q' <> help "Do not print any output.")
  <*> switch
      ( long "noMetasSummary" <>
        help "Do not print a summary of the metavariables state."
      )
  <*> switch
      ( long "metasReport" <>
        help "Print a detailed report of the metavariables state."
      )
  <*> switch
      ( long "metasOnlyUnsolved" <>
        help "In the metavariable report, only print information about the unsolved metavariables."
      )
  <*> switch
      ( long "noProblemsSummary" <>
        help "Do not print a summary of the unsolved problems."
      )
  <*> switch
      ( long "problemsReport" <>
        help "Print a detailed report of the unsolved problems."
      )
  <*> switch
      ( long "checkMetaConsistency" <>
        help "Check consistency of instantiated term of a metavar and its type."
      )
  <*> switch
      ( long "fastGetAbsName" <>
        help "Do not spend time getting bound names in abstractions."
      )
  <*> switch
      ( long "disableSynEquality" <>
        help "Disable syntactic equality"
      )
  <*> switch
      ( long "dontNormalizePP" <>
        help "Don't normalize terms before pretty printing them"
      )
  <*> switch
      ( long "whnfApplySubst" <>
        help "Reduce term when applying a substitution"
      )
  <*> switch
      ( long "timeSections" <>
        help "Measure how much time is taken by each debug section"
      )
  <*> switch
      ( long "whnfEliminate" <>
        help "Reduce term when eliminating a term"
      )
  <*> outputModeOption
      (long "outputMode" <> short 'm' <>  
       help "enter tc/typcheck for type checking or i/interpret for interpreting the expression into a target language.")
  <*> targetLanguageOption
      (long "targetLanguage" <> short 'l' <> value Tog <>
       help "choose a target language: tog, lean, agda, agda-pred-style")
  <*> strOption
      ( long "destFolder" <> short 'f' <> value "generated" <>
        help "enter the path to the destination folder")

debugLabelsOption
  :: Mod OptionFields DebugLabels
  -> Parser DebugLabels
debugLabelsOption = option $ do
  s <- readerAsk
  case s of
    [] -> return DLAll
    _  -> return $ DLSome $ splitOn "|" s

outputModeOption :: Mod OptionFields Mode
  -> Parser Mode
outputModeOption = option $ do
  s <- readerAsk
  case s of
    "i" -> return Interpret
    "interpret" -> return Interpret
    "tc" -> return TypeCheck
    "typecheck" -> return TypeCheck 
    _ -> error "Please provide the operation mode using `-m` option. Enter tc or typecheck to type check tog files or enter i or interpret to interpret theory expressions"
  
targetLanguageOption :: Mod OptionFields TargetLanguage
  -> Parser TargetLanguage
targetLanguageOption = option $ do
  s <- readerAsk
  case s of
    "tog" -> return Tog
    "agda" -> return Agda
    "agda-pred-style" -> return AgdaPredStyle
    "lean" -> return Lean
    _ -> return Tog
    

parseMain :: Parser (IO ())
parseMain =
  typeCheck
    <$> argument str (metavar "FILE")
    <*> parseTypeCheckConf
  where
    typeCheck file conf = do
      instrument conf $ do
        omode <- outputMode <$> readConf
        case omode of
          TypeCheck ->
            processFile file $ \_ mbErr -> do
                forM_ mbErr $ \err -> do
                  silent <- confQuiet <$> readConf
                  unless silent $ putStrLn (PP.render err)
                  exitFailure
          Interpret -> do
            target <- targetLang <$> readConf 
            dir <- destFolder <$> readConf 
            Export.main dir target file  

{- The processing of the file goes as follows: 
     s <- readFile file
     raw <- parseModule 
     mod <- scopeCheckModule raw
     case mod of
       Left err -> putStrLn $ show $ err 
       Right int -> putStrLn $ show $ SA.morePretty int 
-} 
processFile
  :: FilePath
  -> (forall t. (IsTerm t) => Signature t -> Maybe PP.Doc -> IO a)
  -> IO a
processFile file ret =
  do
    mbErr <- runExceptT $ do
      s   <- lift $ readFile file
      raw <- exceptShowErr "Parse" $ parseModule s
      exceptShowErr "Scope" $ scopeCheckModule raw
    case mbErr of
      Left err  -> ret (sigEmpty :: Signature Simple) (Just err)
      Right int -> -- timeIt $
                    checkFile int $ \sig mbErr' ->
                      ret sig (showError "Type" <$> mbErr')
  where
    showError errType err =
      PP.text errType <+> "error: " $$ PP.nest 2 err

    exceptShowErr errType =
      ExceptT . return . either (Left . showError errType) Right

main :: IO ()
main = do
        join $ execParser $ info (helper <*> parseMain) fullDesc 

