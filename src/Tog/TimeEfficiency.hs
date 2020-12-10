{-# LANGUAGE OverloadedStrings #-}

module Tog.TimeEfficiency where

import Tog.Raw.Abs
import Tog.Parse 
import Tog.ScopeCheck
import Tog.Deriving.Main 
import Tog.Exporting.Agda

import Formatting
import Formatting.Clock
import System.Clock


timeTest :: FilePath -> IO () 
timeTest file =
  do s <- readFile file
     case parseModule s of
       Left err -> putStrLn $ show $ err
       Right raw -> timeTestHelper raw 
         
timeTestHelper :: Module -> IO ()
timeTestHelper (Module _ _ (Lang_ defs)) = do
  -- Flattening time 
  start <- getTime Monotonic
  flattenedModule <- pure $ defsToModule defs
  flattenTime <- getTime Monotonic

  -- Generation time 
  fullModule <- pure $ processModule flattenedModule
  generationTime <- getTime Monotonic

  -- Scope-Checking time
  _ <- pure $ scopeCheckModule fullModule
  scopeCheckingTime <- getTime Monotonic

  -- Exporting time
  beforeExport <- getTime Monotonic
  _ <- pure $ exportAgda "Test" fullModule
  afterExport <- getTime Monotonic
  
  fprint (" flattening time: " % timeSpecs) start flattenTime
  fprint ("\n Generation time:" % timeSpecs) flattenTime generationTime
  fprint ("\n Scope-Checking time:" % timeSpecs) generationTime scopeCheckingTime
  fprint ("\n Exporting time:" % timeSpecs) beforeExport afterExport
  fprint ("\n") 
timeTestHelper _ = putStrLn "error"   


