
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
normalDist :: VarName -> CExpr -> ParamName -> Dist
normalDist var mu muParam =
  DoubleDist
  (Log.ln $
   normalDensityUnchecked mu 1 (VarExpr var))
  [(muParam, (VarExpr var - mu))]

testDPMix :: DPMix
--testDPMix =
--  DPMix
--  { clusterDist =
--      -- double cluster_pdf(union value *x0)
--      TupleDist [uniformDist (VarName 0) 0 100
--                ,uniformDist (VarName 1) 0 100]
--  , valuesDist =
--      -- double value_pdf(union value *x0, union value *x1)
--    TupleDist
--    [uniformDist (VarName 1) 0 (TupleProjExpr [DoubleType, DoubleType] (VarExpr (VarName 0)) 0),
--     uniformDist (VarName 2) 0 (TupleProjExpr [DoubleType, DoubleType] (VarExpr (VarName 0)) 1),
--     normalDist (VarName 3) (TupleProjExpr [DoubleType, DoubleType] (VarExpr (VarName 0)) 0) (ParamName 0),
--     normalDist (VarName 4) (TupleProjExpr [DoubleType, DoubleType] (VarExpr (VarName 0)) 1) (ParamName 1)]
--  }

testDPMix =
  DPMix { clusterDist = uniformDist (VarName 0) 0 100
        , valuesDist = uniformDist (VarName 1) 10 50 }

main :: IO ()
main = putStrLn (showDPMix testDPMix)
