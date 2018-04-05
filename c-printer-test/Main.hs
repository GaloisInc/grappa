
module Main where

import qualified Numeric.Log as Log

import Language.Grappa.Distribution
import Language.Grappa.Interp.CExpr
import Language.Grappa.Inference.CPrinter

uniformDist :: VarName -> CExpr -> CExpr -> AtomicDist
uniformDist var lo hi =
  DoubleDist
  (CondExpr
   -- If (lo <= var && var <= hi)
   (BinaryExpr
    AndOp
    -- lo <= var
    (BinaryExpr LTEOp lo (VarExpr DoubleType var))
    -- var <= hi
    (BinaryExpr LTEOp (VarExpr DoubleType var) hi)
   )
   -- Then return log (1 / (hi - lo))
   (log (1 / (hi - lo)))
   -- Else return -INF
   (log 0))
  -- No gradients for the uniform dist
  []

-- | Build a normal distribution with mean given by a variable and variance 1
normalDist :: VarName -> VarName -> AtomicDist
normalDist var mu =
  DoubleDist
  (Log.ln $
   normalDensityUnchecked (VarExpr DoubleType mu) 1 (VarExpr DoubleType var))
  [(var, VarExpr DoubleType mu - VarExpr DoubleType var),
   (mu, (VarExpr DoubleType var - VarExpr DoubleType mu))]

testDPMix :: DPMix
testDPMix =
  DPMix
  { clusterDist =
      TupleDist [uniformDist (ParamVar 0) 0 100]
  , valuesDist =
    TupleDist
    [uniformDist (ValueVar 0) 0 (VarExpr DoubleType (ParamVar 0)),
     uniformDist (ValueVar 1) 0 (VarExpr DoubleType (ParamVar 0)),
     normalDist (ValueVar 2) (ParamVar 0),
     normalDist (ValueVar 3) (ParamVar 0)]
  }

main :: IO ()
main = putStrLn (showDPMix testDPMix)
