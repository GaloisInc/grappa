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
