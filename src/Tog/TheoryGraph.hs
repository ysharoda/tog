module TheoryGraph where

import Data.Map 
import Tog.Raw.Abs


data Theory = Theory{
                name   :: String,
                params :: Params,
                fields :: Fields } 

-- type 

data View   = View{
                source :: Theory, 
                target :: Theory,
                map    :: [(Constr,Constr)] }

data TGraph = TGraph{
                nodes :: Map String Theory,
                edges :: Map String View }

              
-- extendTheory :: Theory -> [Constr] -> (View,Theory)


-- renameTheory :: Theory -> View -> (View,Theory) 
