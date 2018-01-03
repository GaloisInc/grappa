{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Language.Grappa.Inference.GradientDescent where

import Control.Monad ( replicateM )

import Language.Grappa.Distribution

import Debug.Trace

-- For debugToFile
import System.IO.Unsafe

debugFilename :: String
debugFilename = "gd-debug"

clearDebugFile :: a -> a
clearDebugFile expr = unsafePerformIO $ do
  writeFile debugFilename ""
  return expr

debugToFile :: String -> a -> a
debugToFile str expr = unsafePerformIO $ do
  appendFile debugFilename str
  return expr

----------------------------------------------------------------
-- * Gradient descent
--
-- $gd
--
-- We provide two gradient descent implementations, 'gd1' and
-- 'gd2'. You probably want to use 'gd2'.
----------------------------------------------------------------

-- Some ideas for ensuring we do keep making progress when
-- we can, by not decreasing the step size unnecessarily:
--
-- 1.  don't decrease the step size until the objective function stops
--     improving "fast enough", as determined by (3) above.
--
-- 2.  split the AdaGrad step size into two parts, a scalar learning
--     rate (@eta@ or @rho@ in the papers) and normalized AdaGrad
--     learning rate vector. That is, in place of
--
--     > diag(G^t)^{-1/2}
--
--     we use
--
--     > eta^t (d^t / || d^t ||_2)
--
--     for some @d^t@ based on @diag(G^t)^{-1/2}@.
--
--     While this approach punts a bit, by depending on a new
--     scalar learning rate @eta@, it simpler in that it decouples
--     the per component learning rate / emphasis part of AdaGrad,
--     a vector, from the scalar decrease in the step size. We can
--     use a notion of decreasing progress as above to wind down
--     the scalar learning rate.
--
--     For the @d^t@ we can simply use @diag(G^t)^{-1/2}@ itself,
--     or perhaps a forgetful version, e.g.
--
--     > diag(G^{t-k,t})^{-1/2}
--
--     for
--
--     > G^{t1,t2} := g^{t1} g^{t1}^T + ... + g^{t1} g^{t1}^T
--
--     i.e.
--
--     > G^t = G^{1,t}.

-- | The parameters of a GD optimization probllem.
data GdParams m =
  GdParams { _projectLambda :: Int -> [Double] -> [Double]
             -- ^ Project 2nd argument into the domain of the
             -- objective. The expectation is that
             --
             -- > _projectLambda = projectRectangle <bounds>
             --
             -- where @<bounds>@ describes the domain of the
             -- objective. See 'projectRectangle' for the general case
             -- and 'projectLambdaNormal' for an example
             -- instantiation.
           , _sampleLambda  :: m [Double]
             -- ^ Returns the starting value to initiate the gradient
             -- descent from. Use e.g. 'defaultSampleLambda' or
             -- @return $ replicate <num dimensions> 0@ if you don't
             -- care what the starting value is.
           , _evalObj       :: [Double] -> m Double
             -- ^ The objective function to be optimized.
           , _evalGradObj   :: [Double] -> m [Double]
             -- ^ The gradient of the objective.
           }

-- | The type of GD algorithms.
--
-- The @m@ is always monadic, but adding a @Monad m@ constraint on the
-- RHS here causes problems with "impredicative polymorphism" later,
-- if we try to make a list of @Gd m@s.
type Gd m = GdParams m -> m [Double] {-^ The best @lambda@ we found. -}

-- | Naive gradient descent using harmonic step size.
--
-- __Use 'gd2' instead__!
--
-- Diverges for functions with minimum in steep valley, e.g. @x^4@,
-- since it jumps back and forth across the valley, climbing the walls
-- higher and higher.
--
-- The @epsilon@ is a stopping threshold: the search stops when the
-- distance between two successive points in the search are less than
-- @epsilon@ apart.
gd1 :: Monad m => Double{-^epsilon-} -> Gd m
gd1 epsilon GdParams{..} = do
  lambda <- _projectLambda 1 <$> _sampleLambda
  loop lambda 1
  where
    loop !lambda !t = trace ("t = "++show t++", lambda = "++show lambda) $ do
      grad <- _evalGradObj lambda
      let lambda' = _projectLambda t $
            lambda `subV` (rho t `scaleV` grad)
      let delta = ell1 $ lambda `subV` lambda'
      if delta >= epsilon
        then loop lambda' (t + 1)
        else trace ("Done: t = "++show t++", lambda = "++show lambda') $ return lambda'
    -- Bbvi paper says that any sequence converging in @\ell^2@ and
    -- diverging in @\ell^1@ will do for @rho@ here.
    rho t = 1 / fromIntegral t

-- | Gradient descent using exponential line search with harmonic
-- starting steps.
--
-- The @epsilon@ is a stopping threshold: the search stops when the
-- distance between two successive points in the search are less than
-- @epsilon@ apart.
gd2 :: Monad m => Double{-^epsilon-} -> Gd m
gd2 epsilon GdParams{..} = clearDebugFile $ do
  lambda <- _projectLambda 1 <$> _sampleLambda
  loop lambda 1
  where
    debugLoop lambda@[x_in,y_in] t m =
      let x = fromRealLbUb 0 2 x_in
          y = fromRealLbUb 0 2 y_in in
      debugToFile (show x ++ "," ++ show y ++ "\n") $
      trace ("t = "++show t++", lambda = "++show lambda) $ m
    debugLoop lambda t m =
      trace ("t = "++show t++", lambda = "++show lambda) $ m
    loop !lambda !t = debugLoop lambda t $ do
      step <- _evalGradObj lambda
      traceM $ "step = " ++ show step
      lambda' <- lineSearch (_projectLambda t) step lambda
      --val <- _evalObj lambda
      --val' <- _evalObj lambda'
      traceM "Line search complete"
      traceM $ "lambda = " ++ show lambda ++ ", lambda' = " ++ show lambda'
      --traceM $ "val = " ++ show val ++ ", val' = " ++ show val'
      --let delta = abs (val - val' / val)
      let delta = ell1 $ lambda `subV` lambda'
      if delta >= epsilon
        then loop lambda' (t + 1)
        else trace ("Done: t = "++show t++", lambda = "++show lambda') $ return lambda'

    -- Step lambda in the negative gradient direction to make the
    -- objective smaller. Handles both the case where we can make lots
    -- of progress (@growStep@), and the case where we're in a steep
    -- valley and need to avoid jumping over the bottom
    -- (@shrinkStep@).
    lineSearch !proj !step !lambda = do
      -- If the first step makes progress, then we keep doubling the
      -- step until we stop making progress.
      let growStep !lambda !val !step = do
            let step' = 2 `scaleV` step
            let lambda' = proj $ lambda `subV` step
            val' <- _evalObj lambda'
            traceM ("grow: [val,val'] = "++show [val,val']++", step = "++show step)
            if val' <= val
              then growStep lambda' val' step'
              else return lambda
      -- If the first step doesn't make progress, then we keep halving
      -- the step until we make progress, or the step becomes smaller
      -- than the epsilon cutoff.
      let shrinkStep !lambda !val !step = do
            let step' = (1/2) `scaleV` step
            let lambda' = proj $ lambda `subV` step
            val' <- _evalObj lambda'
            traceM ("shrink: [val,val'] = "++show [val,val']++", step = "++show step)
            if ell1 step < epsilon || val' < val
              then return lambda'
              else shrinkStep lambda val step'
      -- Check how the first step turns out and choose a looping
      -- strategy accordingly.
      val <- _evalObj lambda
      let lambda' = proj $ lambda `subV` step
      val' <- _evalObj lambda'
      let weMadeProgress = val' <= val
      if ell1 step == 0 then
        return lambda
        else if weMadeProgress
             then growStep lambda' val' step
             else shrinkStep lambda val step

    -- Bbvi paper says that any sequence converging in @\ell^2@ and
    -- diverging in @\ell^1@ will do for @rho@ here.
    --rho t = 1 / fromIntegral t


----------------------------------------------------------------
-- * Helpers
----------------------------------------------------------------

-- | Sample a @lambda@ with i.i.d. normal components.
defaultSampleLambda :: SampleableIn m Normal => Int -> m [R]
defaultSampleLambda t = replicateM t $ distSample (Normal 0 10)

-- ** Vector ops defined on lists
addV :: Num a => [a] -> [a] -> [a]
addV = zipWith (+)

subV :: Num a => [a] -> [a] -> [a]
subV = zipWith (-)

-- | Pairwise multiplication.
multV :: Num a => [a] -> [a] -> [a]
multV = zipWith (*)

sumV :: Num a => [[a]] -> [a]
sumV = foldr1 addV

scaleV :: Num a => a -> [a] -> [a]
scaleV s = map (s *)

-- | The @\ell^1@ norm on lists.
ell1 :: Num a => [a] -> a
ell1 = sum . map abs

----------------------------------------------------------------
-- * Projection
----------------------------------------------------------------

-- | One end of an interval.
data Bound = ClosedBound R
           | OpenBound R

fromBound :: Bound -> R
fromBound (ClosedBound b) = b
fromBound (OpenBound b) = b

-- | Project a point @xs@ into the closest point in the rectangle
-- described by @bounds@.
--
-- Note that "closest" is not defined when the rectangle is open on
-- some sides; in this case the result is inside the rectangle and
-- within @1/t@ of the boundary it fell outside of.
projectRectangle :: [(Bound, Bound)] -> Int -> [R] -> [R]
projectRectangle bounds t xs = zipWith projectInterval bounds xs
  where
    projectInterval :: (Bound, Bound) -> R -> R
    projectInterval (lb, ub) x =
      if | x <= fromBound lb ->
           case lb of
             ClosedBound l -> l
             -- If we need to jump back inside past an open bound, we
             -- need to be careful not to jump past the other bound!
             OpenBound l -> min (l + rho t) middle
         | x >= fromBound ub ->
           case ub of
             ClosedBound h -> h
             OpenBound h -> max (h - rho t) middle
         | otherwise -> x
      where
        middle = (fromBound lb + fromBound ub) / 2
        -- Function to use when we fall outside of an open bound: we
        -- go this far back in past the open bound. This is pretty
        -- arbtitrary and I don't think it matters much, as long as it
        -- goes to zero as @t@ goes to infinity.
        rho t = 1 / fromIntegral t
