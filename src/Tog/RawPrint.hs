module Tog.RawPrint where

import Tog.Parse

rawPrint file =
  do s <- readFile file
     return $ parseModule s












