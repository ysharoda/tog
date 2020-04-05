module Tog.Deriving.Debug (test) where

import           Tog.Raw.Abs
import           Tog.Parse

import           Tog.Deriving.Main (processDefs)

test :: FilePath -> IO Module 
test file =
  do s <- readFile file
     case (parseModule s) of
       Right (Module _ _ (Lang_ defs)) ->
        do putStrLn "Generating Hom"
           return $ processDefs defs
       Right _ -> error "Invalid declaration"
       Left _ -> error "Cannot create modules"     

