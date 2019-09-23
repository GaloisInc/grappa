{-# LANGUAGE RankNTypes, TypeFamilies, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}

-- | A monad that supports random generation of values as well as fork-join
-- parallelism

module Language.Grappa.Rand.MWCRandM where

import Language.Grappa.Distribution

import Control.Monad
import Control.Monad.State
import Control.Monad.Primitive

import qualified Data.Vector as V
import qualified Numeric.Log as Log

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

import qualified Control.Monad.Par.IO as Par
import qualified Control.Monad.Par.Class as Par

import qualified Numeric.AD.Mode.Forward as AD
import qualified Numeric.AD.Internal.Forward as AD

-- | FIXME: documentation!
newtype MWCRandM a = MWCRandM { unMWCRandM :: StateT [MWC.GenIO] IO a }
                deriving (Functor, Applicative, Monad)

type Rand = MWCRandM

{-
instance MonadState [MWC.Gen (PrimState IO)] MWCRandM where
  get = MWCRandM get
  put = MWCRandM . put
-}

instance PrimMonad MWCRandM where
  type PrimState MWCRandM = PrimState IO
  primitive f = MWCRandM $ primitive f

instance MonadIO MWCRandM where
  liftIO m = MWCRandM $ liftIO m

runMWCRandMWithSeeds :: MWCRandM a -> [MWC.GenIO] -> IO a
runMWCRandMWithSeeds (MWCRandM m) gs = fst <$> runStateT m gs

runRand :: MWC.GenIO -> MWCRandM a -> IO a
runRand g m = runMWCRandMWithSeeds m [g]

runMWCRandM :: MWCRandM a -> IO a
runMWCRandM m = runMWCRandMWithSeeds m []

-- | Get the current list of seeds
getGenIOs :: MWCRandM [MWC.GenIO]
getGenIOs = MWCRandM get

-- | Ensure that we have at least @n@ seeds
ensureNSeeds :: Int -> MWCRandM ()
ensureNSeeds n =
  do gs <- getGenIOs
     if n <= length gs then return () else
       do gs' <- liftIO $ replicateM (n - length gs) MWC.createSystemRandom
          MWCRandM $ put (gs ++ gs')

-- | Get the @n@th 'GenIO', creating it if necessary
nthGenIO :: Int -> MWCRandM MWC.GenIO
nthGenIO n =
  do ensureNSeeds (n+1)
     gs <- getGenIOs
     return (gs !! n)

-- | An object which can generate random objects
type Sampleable a = forall m. PrimMonad m => MWC.Gen (PrimState m) -> m a

-- | Generate a random value in 'MWCRandM' from a sampler
random :: Sampleable a -> MWCRandM a
random f = do
  gen <- nthGenIO 0
  f gen

-- | Generate a discrete value from a list of relative probabilities
mwcCategorical :: [Prob] -> MWCRandM Int
mwcCategorical probs =
  random $ MWC.logCategorical $ V.fromList $ map (Log.ln . fromProb) probs

-- | Generate a uniformly random variable in 'MWCRandM'
mwcUniform :: Double -> Double -> MWCRandM Double
mwcUniform lo hi = random $ MWC.uniformR (lo, hi)

-- | Generate a normal random variable in 'MWCRandM'
mwcNormal :: Double -> Double -> MWCRandM Double
mwcNormal mu sigma = random $ MWC.normal mu sigma

-- | Generate a random variable from the exponential distribution in 'MWCRandM'
mwcExponential :: Double -> MWCRandM Double
mwcExponential rate = random $ MWC.exponential rate

-- | Generate a gamma random variable in 'MWCRandM'
mwcGamma :: Double -> Double -> MWCRandM Double
mwcGamma k theta = random $ MWC.gamma k theta

-- | Generate a dirichlet-distributed list
mwcDirichlet :: [R] -> MWCRandM [R]
mwcDirichlet alphas = random $ MWC.dirichlet alphas

-- | FIXME: documentation!
parMapM :: (a -> MWCRandM b) -> [a] -> MWCRandM [b]
parMapM f xs =
  do ensureNSeeds (length xs)
     gs <- getGenIOs
     liftIO $ Par.runParIO $
       do futs <- zipWithM (\x g ->
                             Par.spawn_ $ liftIO $
                             runMWCRandMWithSeeds (f x) [g])
            xs gs
          mapM Par.get futs


----------------------------------------------------------------------
-- Drawing Random Variables in Log Space
----------------------------------------------------------------------

-- FIXME: We currently draw from the uniform distribution in log space by
-- drawing from the uniform distribution in standard space and then taking the
-- log, but this loses precision. The preferred method would be to generate a
-- sample @U ~ exponential@ and then return @-U@, except that the standard way
-- to sample from the exponential distribution is to use this trick the other
-- way, sampling from the uniform and then taking the negative log. So figuring
-- out a better way to do this would require some work...
instance MWC.Variate (Log.Log Double) where
  uniform gen = Log.Exp <$> log <$> MWC.uniform gen
  uniformR (Log.Exp lo,Log.Exp hi) gen =
    Log.Exp <$> log <$> MWC.uniformR (lo,hi) gen

-- | Sample the @gamma(k,theta)@ distribution in log space. When @k*theta@ gets
-- very small (as in, between @0@ and @2^-20@ or so), just sampling the @gamma@
-- distribution in standard space and then taking the logarithm tends to yield
-- numbers that are too small to represent as 'Double's, and so they get
-- truncated to 0. So, instead, this function does the entire sampling procedure
-- in log space.
--
-- This code is adapted from the existing code for 'MWC.gamma'.
mwcGammaLogLog :: Log.Log Double -> Log.Log Double -> MWCRandM (Log.Log Double)
mwcGammaLogLog a b = mainloop where
  mainloop = do
    (x, v) <- innerloop
    u      <- random MWC.uniform
    let cont =  u > 1 - 0.331 * sqr (sqr x)
          && log u > 0.5 * sqr x + a1_std * (1 - v + log v) -- Rarely evaluated
    case () of
      _| cont      -> mainloop
       | a >= 1    -> return $! a1 * Log.Exp (log v) * b
       | otherwise -> do y <- random MWC.uniform
                         return $! y ** (1 / a) * a1 * Log.Exp (log v) * b
  -- inner loop
  innerloop = do
    x <- random MWC.standard
    case 1 + a2*x of
      v | v <= 0    -> innerloop
        | otherwise -> return $! (x, (v*v*v))

  sqr x = x*x

  -- constants
  a' = if a < 1 then a + 1 else a
  a1 = a' - 1/3
  a1_std = exp $ Log.ln a1
  a2 = 1 / sqrt(9 * a1_std)


mwcGammaLog :: Double -> Double -> MWCRandM (Log.Log Double)
mwcGammaLog a b | a >= 1 = Log.Exp <$> log <$> mwcGamma a b
mwcGammaLog a b =
  do x <- mwcGammaLog (a+1) b
     y <- random MWC.uniform
     return $ Log.Exp (Log.ln y / a) * Log.Exp (log (a+2/3)) * x


-- | Sample a Dirichlet distribution in log space
mwcDirichletLogLog :: [Log.Log R] -> MWCRandM [Log.Log R]
mwcDirichletLogLog alphas =
  do raw_xs <- mapM (\alpha -> mwcGammaLogLog alpha 1) alphas
     let total = sum raw_xs
     return $ map (/ total) raw_xs

-- | Sample a Dirichlet distribution in log space
mwcDirichletLog :: [R] -> MWCRandM [Log.Log R]
mwcDirichletLog alphas =
  do raw_xs <- mapM (\alpha -> mwcGammaLog alpha 1) alphas
     let total = sum raw_xs
     return $ map (/ total) raw_xs


----------------------------------------------------------------------
-- Implementing various distributions in MWCRandM
----------------------------------------------------------------------

instance SampleableIn MWCRandM StdNormal where
  distSample StdNormal = random MWC.standard

instance SampleableIn MWCRandM Normal where
  distSample (Normal mu sigma) = mwcNormal mu sigma

instance SampleableIn MWCRandM Uniform where
  distSample (Uniform lo hi) = mwcUniform lo hi

instance SampleableIn MWCRandM (Dirac a) where
  distSample (Dirac x) = return x

instance SampleableIn MWCRandM (DontCare a) where
  distSample (DontCare x) = return x

instance SampleableIn MWCRandM Categorical where
  distSample (Categorical xs) = do
    let mx = sum xs
    p <- random $ MWC.uniformR (0, probToR mx)
    return $ go 0 (rToProb p) xs
      where go _ _ [] = error "unreachable"
            go i n (y:ys)
              | n < y     = i
              | otherwise = go (i+1) (n-y) ys

instance SampleableIn MWCRandM Cauchy where
  distSample Cauchy = do
    x <- distSample StdNormal
    y <- distSample StdNormal
    return $ x/y

instance ReprSampleableIn MWCRandM ReprNormal AD.Forward where
  distSampleRepr (ReprNormal mu sigma) =
    fmap AD.auto $ random $ MWC.normal (AD.primal mu) (AD.primal sigma)

instance ReprSampleableIn MWCRandM ReprUniform AD.Forward where
  distSampleRepr (ReprUniform lo hi) =
    fmap AD.auto $ random $ MWC.uniformR (AD.primal lo, AD.primal hi)
