{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Grappa.Inference.Util where

import Data.IORef
import Control.Monad.Reader

import Debug.Trace

import Language.Grappa.Distribution
import Language.Grappa.Rand.MWCRandM


----------------------------------------------------------------------
-- * Debugging Support
----------------------------------------------------------------------

-- | Flag to turn on debugging
debugFlag :: Bool
debugFlag = True -- Set to False to disable tracing

-- | Trace iff debugging is turned on
dtrace :: String -> a -> a
dtrace str a | debugFlag = trace str a
dtrace _ a = a


----------------------------------------------------------------------
-- * A Monad for Sampling-Based Inference Methods
----------------------------------------------------------------------

-- | A sampling computation is a stochastic / random computation along with a
-- continuation that consumes samples of type @samp@
newtype SamplingM samp a =
  SamplingM { unSamplingM :: ReaderT (samp -> MWCRandM ()) MWCRandM a }
  deriving (Functor, Applicative, Monad)

-- | Emit a sample that has been generated
emitSample :: samp -> SamplingM samp ()
emitSample s = SamplingM $ do
  k <- ask
  lift $ k s

-- | Lift an 'MWCRandM' computation into a 'SamplingM' computation
liftMWCRandM :: MWCRandM a -> SamplingM samp a
liftMWCRandM m = SamplingM $ lift m

-- | Run a 'SamplingM' computation, passing in a continuation to consume samples
runSamplingM :: (samp -> MWCRandM ()) -> SamplingM samp a -> MWCRandM a
runSamplingM k (SamplingM m) = runReaderT m k

-- | Collect all the samples of a 'SamplingM' computation in a list
listifySamplingM :: SamplingM samp () -> MWCRandM [samp]
listifySamplingM m =
  do rev_ptr <- liftIO $ newIORef []
     runSamplingM (sampling_k rev_ptr) m
     reverse <$> liftIO (readIORef rev_ptr)
     where
       sampling_k rev_ptr samp =
         liftIO $ modifyIORef rev_ptr (samp :)

-- | Collect the last sample of a 'SamplingM' computation
lastSamplingM :: SamplingM samp () -> MWCRandM samp
lastSamplingM m =
  do ptr <- liftIO $ newIORef Nothing
     runSamplingM (liftIO . writeIORef ptr . Just) m
     maybe_v <- liftIO (readIORef ptr)
     case maybe_v of
       Just v -> return v
       Nothing -> error "lastSamplingM"

-- | Generate a uniformly distributed value in a 'SamplingM' computation
genUniform :: Double -> Double -> SamplingM samp Double
genUniform low high = SamplingM $ lift $ mwcUniform low high

-- | Generate a normally distributed value in a 'SamplingM' computation
genNormal :: Double -> Double -> SamplingM samp Double
genNormal mu sigma = SamplingM $ lift $ mwcNormal mu sigma

-- | Generate a discrete value from a list of relative probabilities
genCategorical :: [Prob] -> SamplingM samp Int
genCategorical = SamplingM . lift . mwcCategorical

-- | Generate a Boolean, of value 'True' with probability @'max' ('min' 1 p) 0@
genBernoulli :: Double -> SamplingM samp Bool
genBernoulli p =
  do u <- genUniform 0 1
     return $ u <= p

-- | Generate a Boolean, of value 'True' with probability @'min' 1 ('exp' logP)@
genBernoulliLog :: Double -> SamplingM samp Bool
genBernoulliLog logp =
  -- Evaluate the non-exponentiated probability first to avoid overflow in
  -- exponentiation in case it is large. Also, we avoid a superfluous random
  -- draw this way.
  if logp >= 0 then return True else genBernoulli (exp logp)

-- | Generate a value sampled from the exponential distribution
genExponential :: Double -> SamplingM samp Double
genExponential rate = SamplingM $ lift $ mwcExponential rate

-- | Probabilistically return one of two values, choosing the first with
-- probability @p@
randomIf :: Double -> a -> a -> SamplingM samp a
randomIf p _ _ | isNaN p = error "randomIf: NaN probability!"
randomIf p a1 a2 =
  do b <- genBernoulli p
     if b then return a1 else return a2

-- | Probabilistically return one of two values, choosing the first with
-- probability @'exp' logp@
randomIfLog :: Double -> a -> a -> SamplingM samp a
randomIfLog logp a1 a2 =
  do b <- genBernoulliLog logp
     if b then return a1 else return a2
