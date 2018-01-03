{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Grappa.Test.Inference.GradientDescent where

import           Control.Monad ( forM, forM_, replicateM )
import qualified Numeric.LinearAlgebra as La
import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.StudentT as S
import qualified System.Random.MWC as MWC

import           Test.Hspec
import qualified Test.QuickCheck as Qc
import qualified Test.QuickCheck.Monadic as Qc
import qualified Test.QuickCheck.Property as Qc

import           Language.Grappa.Distribution
import           Language.Grappa.Rand.MWCRandM
import           Language.Grappa.Inference.GradientDescent

tests :: Spec
tests = do
  forM_ [1..8] $ \ x ->
    it ("should pass this QC test with k=" ++ show x) $
      prop_evalGradLogMVNormalDensity_correct x

-- | QuickCheck property asserting 'compareGrads' for given mv normal
-- dimension @k@.
prop_evalGradLogMVNormalDensity_correct :: Int -> Qc.Property
prop_evalGradLogMVNormalDensity_correct k =
  -- forAll' "k" Qc.arbitrary $ \(Qc.Positive (k :: Int)) ->
  forAll' "xList" (Qc.vector k) $ \xList ->
  forAll' "muList" (Qc.vector k) $ \muList ->
  forAll' "cList" (genCList k) $ \cList ->
  Qc.monadicIO $ do
    deltas <- Qc.run $ compareGrads k (i xList) (i $ muList ++ cList)
    Qc.monitor (Qc.counterexample $ "(Index, Delta): " ++ show (argMax deltas))
    Qc.assert $ all isSmall deltas
  where
    -- Return index of max entry, and max entry.
    argMax :: Ord a => [a] -> (Int, a)
    argMax (x:xs) = go 1 (0,x) xs
      where
        go _ p [] = p
        go j (i,x) (x':xs) = go (j+1) (if x < x' then (j, x') else (i, x)) xs

    i :: [Integer] -> [Double]
    i = map fromInteger
    -- Generate a list representation of a Cholesky factor. The
    -- strategy is to recursively generate row tails from the diagonal
    -- entry onwards, with non-zero diagonal entries and arbitrary
    -- other entries.
    genCList :: Int -> Qc.Gen [Integer]
    genCList k = do
      rows <- forM [k,k-1..1] $ \len -> do
        Qc.Positive diagEntry <- Qc.arbitrary
        rest <- Qc.vectorOf (len-1) Qc.arbitrary
        return $ diagEntry : rest
      return $ concat rows

    isSmall delta = abs delta <= 0.001

    -- A version of @Qc.forAll@ with named quantifiers. This makes the
    -- counterexamples much easier to read.
    forAll' name gen pf =
      -- The library provided @Qc.forAll@ that I adapted to create
      -- this @forAll'@ has a @Qc.again@ here. But I don't understand
      -- why I need it, and more importantly, I get an import error,
      -- so leaving it out ...
      --
      -- Qc.again $
      Qc.MkProperty $
      gen >>= \x ->
        Qc.unProperty $
        Qc.counterexample (name++": "++show x) (pf x)

-- | Check the QuickCheck props @numTrials@ many times.
--
-- For larger @k@ this fails, but I think it's due to numerical
-- instability. For small @k@, e.g. less than or equal to 5, we can
-- pass hundreds of thousands of tests. For large @k@, e.g. @k = 30@,
-- we fail pretty fast.
checkProps :: Int -> Int -> IO ()
checkProps k numTrials = do
  qc $ prop_evalGradLogMVNormalDensity_correct k
  where
    qc = Qc.quickCheckWith (Qc.stdArgs { Qc.maxSuccess = numTrials })


-- | For example:
--
-- > runGdTest (gd2 0.001) (gdTest3 4 [1,42])
runGdTest :: Gd Rand -> GdTest Rand -> IO (Double, [Double])
runGdTest gd GdTest{..} = do
  -- Use 'MWC.create' instead if you want repeatable/predictable
  -- results.
  g <- MWC.createSystemRandom
  lambda <- runRand g $ gd _gdParams
  return (_estimateError lambda, lambda)

----------------------------------------------------------------
-- * Tests
----------------------------------------------------------------

data GdTest m = GdTest
  { _gdParams      :: GdParams m
  , _estimateError :: [Double] -> Double
  }

-- | Test for objective function @f x = (x - 42)**2@, which is
-- minimized at @x = 42@.
gdTest1 :: SampleableIn m Normal => GdTest m
gdTest1 = GdTest
  { _gdParams = GdParams
    { _projectLambda = const id
    , _sampleLambda = defaultSampleLambda 1
    , _evalObj = \[x] -> return $ (x - center!!0)**2
    , _evalGradObj = \[x] -> return [2 * (x - center!!0)]
    }
  , _estimateError = \lambda -> ell1 $ lambda `subV` center
  }
  where
    center = [42]

-- | Test for objective function @f [x,y] = ([x,y] - [42,10^6])**2@,
-- which is minimized at @[42,10^6]@.
gdTest2 :: SampleableIn m Normal => GdTest m
gdTest2 = GdTest
  { _gdParams = GdParams
    { _projectLambda = const id
    , _sampleLambda = defaultSampleLambda 2
    , _evalObj = \[x,y] -> return $ sqrt ( (x - center!!0)**2
                                         + (y - center!!1)**2 )
    , _evalGradObj = \[x,y] -> return [ 2 * (x - center!!0)
                                      , 2 * (y - center!!1) ]
    }
  , _estimateError = \lambda -> ell1 $ lambda `subV` center
  }
  where
    center = [ 42, 1000000 ]

-- | Test for objective function @f x = (x - center)**k@ where
-- @center@ is an arbitrary vector. The dimension of @center@
-- determines the dimension of @x@. The objective is minimized at
-- @center@ for even powers @k@, and has no minimum for odd powers
-- @k@. You're on your own for fractional powers.
gdTest3 :: SampleableIn m Normal => Double -> [Double] -> GdTest m
gdTest3 k center = GdTest
  { _gdParams = GdParams
    { _projectLambda = const id
    , _sampleLambda = defaultSampleLambda (length center)
    , _evalObj = \lambda -> return $ (ell2 $ v lambda)**k
    , _evalGradObj = \lambda -> return
        [ k * (ell2 (v lambda))**(k-2) * vi
        | vi <- v lambda ]
    }
  , _estimateError = \lambda -> ell1 $ lambda `subV` center
  }
  where
    v lambda = lambda `subV` center

-- | Test for objective function
--
-- > f x = (x - center)**k -
-- >       amplitude * cos (2pi * |x - center| / period)
--
-- I.e. like 'gdTest3', but with an added noise factor of @- cos@ to
-- introduce infinitely many local minima. This is a better test of
-- the line search in 'gd2'. I expect that making the period and
-- amplitude large enough, and the center far enough from the origin,
-- would trick 'gd2' into a local minium, but I can't find parameters
-- that actually do this!
--
-- This objective is minimized at @center@ for even powers @k@, like
-- 'gdTest3'.
gdTest4 :: SampleableIn m Normal =>
  Double -> [Double] -> Double -> Double -> GdTest m
gdTest4 k center amplitude period = GdTest
  { _gdParams = GdParams
    { _projectLambda = const id
    , _sampleLambda = defaultSampleLambda (length center)
    , _evalObj = \lambda ->
        return $ (ell2 $ v lambda)**k -
                 amplitude * cos (2 * pi *
                                  (ell2 $ v lambda) / period)
    , _evalGradObj = \lambda -> return
        [ k * (ell2 (v lambda))**(k-2) * vi +
          sin (ell2 (v lambda)) *
            (2 * pi / period) *
            vi / ell2 (v lambda)
        | vi <- v lambda ]
    }
  , _estimateError = \lambda -> ell1 $ lambda `subV` center
  }
  where
    v lambda = lambda `subV` center

----------------------------------------------------------------
