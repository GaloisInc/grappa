module Main where

import qualified Language.Grappa.Test.Numeric as Numeric
import qualified Language.Grappa.Test.Parsing as Parsing
--import qualified Language.Grappa.Test.Inference.GradientDescent as GD
import Test.Hspec as HS

main :: IO ()
main = HS.hspec $ do
  HS.describe "Numeric types" Numeric.tests
  HS.describe "Grappa parsing" Parsing.tests
  HS.describe "inference methods" $ do
    return ()
--    HS.describe "gradient descent" GD.tests
