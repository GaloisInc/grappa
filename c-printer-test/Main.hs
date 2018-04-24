
module Main where

import qualified Numeric.Log as Log

import Language.Grappa.Distribution
import Language.Grappa.Interp.CExpr
import Language.Grappa.Inference.CPrinter

uniformDist :: VarName -> CExpr -> CExpr -> Dist
uniformDist var lo hi =
  DoubleDist
  (CondExpr
   -- If (lo <= var && var <= hi)
   (BinaryExpr
    AndOp
    -- lo <= var
    (BinaryExpr LteOp lo (VarExpr var))
    -- var <= hi
    (BinaryExpr LteOp (VarExpr var) hi)
   )
   -- Then return log (1 / (hi - lo))
   (log (1 / (hi - lo)))
   -- Else return -INF
   (log 0))
  -- No gradients for the uniform dist
  []

-- | Build a normal distribution with mean given by a variable and variance 1
normalDist :: VarName -> VarName -> Dist
normalDist var mu =
  DoubleDist
  (Log.ln $
   normalDensityUnchecked (VarExpr mu) 1 (VarExpr var))
  [(var, VarExpr mu - VarExpr var),
   (mu, (VarExpr var - VarExpr mu))]

testDPMix :: DPMix
testDPMix =
  DPMix
  { clusterDist =
      TupleDist [uniformDist (VarName 0) 0 100]
  , valuesDist =
    TupleDist
    [uniformDist (VarName 1) 0 (VarExpr (VarName 0)),
     uniformDist (VarName 2) 0 (VarExpr (VarName 0)),
     normalDist (VarName 3) (VarName 0),
     normalDist (VarName 4) (VarName 0)]
  }

main :: IO ()
main = putStrLn (showDPMix testDPMix)
