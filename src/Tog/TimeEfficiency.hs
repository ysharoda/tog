{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Tog.TimeEfficiency where

{- ---- using $! ------ 
*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 26.57 us
 Generation time:9.44 us
 Scope-Checking time:14.41 s
 Exporting time:1.26 ms
*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 10.38 us
 Generation time:7.08 us
 Scope-Checking time:12.92 s
 Exporting time:18.70 us
*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 9.65 us
 Generation time:7.49 us
 Scope-Checking time:12.98 s
 Exporting time:7.64 us
*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 10.75 us
 Generation time:6.72 us
 Scope-Checking time:12.96 s
 Exporting time:7.60 us

-- --------- using $!! and implemented instances of 

*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 5.42 s
 Generation time:3.26 s
 Scope-Checking time:7.85 s
 Exporting time:8.89 us
*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 4.87 s
 Generation time:2.93 s
 Scope-Checking time:6.44 s
 Exporting time:7.75 us
*Tog.TimeEfficiency> timeTest "../../Library/mathscheme.tog"
 flattening time: 4.75 s
 Generation time:3.09 s
 Scope-Checking time:6.77 s
 Exporting time:11.34 us

-} 


import Tog.Raw.Abs
import Tog.Parse 
import Tog.ScopeCheck
import Tog.Deriving.Main 
import Tog.Exporting.Agda

import Formatting
import Formatting.Clock
import System.Clock
import Control.DeepSeq
import Text.PrettyPrint.Leijen

import Tog.TimeTest.NFAModule()
import Tog.TimeTest.NFModule()

instance NFData Doc where
  rnf doc = doc `seq` ()  

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
  flattenedModule <- pure $!! defsToModule defs
  flattenTime <- getTime Monotonic

  -- Generation time 
  fullModule <- pure $!! processModule flattenedModule
  generationTime <- getTime Monotonic

  -- Scope-Checking time
  _ <- pure $!! scopeCheckModule fullModule
  scopeCheckingTime <- getTime Monotonic

  -- Exporting time
  beforeExport <- getTime Monotonic
  _ <- pure $!! exportAgda "Test" fullModule
  afterExport <- getTime Monotonic
  
  fprint (" flattening time: " % timeSpecs) start flattenTime
  fprint ("\n Generation time:" % timeSpecs) flattenTime generationTime
  fprint ("\n Scope-Checking time:" % timeSpecs) generationTime scopeCheckingTime
  fprint ("\n Exporting time:" % timeSpecs) beforeExport afterExport
  fprint ("\n") 
timeTestHelper _ = putStrLn "error"   


