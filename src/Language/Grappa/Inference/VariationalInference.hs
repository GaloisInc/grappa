{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Language.Grappa.Inference.VariationalInference where

import Control.Monad ( forM, replicateM )
import Data.List ( transpose )

import Control.Lens ( (.~) )
import qualified Data.Colour as G
import qualified Data.Colour.Names as G
import qualified Data.Default.Class as G
import qualified Data.Matrix as Dm
import qualified Graphics.Rendering.Chart as G
import qualified Graphics.Rendering.Chart.Backend.Diagrams as G
import qualified Numeric.AD as Ad
import qualified Numeric.LinearAlgebra as La
import Numeric.LinearAlgebra ( Matrix, Vector, (<>), (<.>), (#>) )
import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.StudentT as S
import qualified System.Random.MWC as MWC
import qualified Test.QuickCheck as Qc
import qualified Test.QuickCheck.Monadic as Qc
import qualified Test.QuickCheck.Property as Qc

import Language.Grappa.Distribution
import Language.Grappa.Inference.GradientDescent
import Language.Grappa.Rand.MWCRandM

import Debug.Trace

----------------------------------------------------------------
-- * BBVI algorithms
----------------------------------------------------------------
--
-- $bbviAlgorithms
-- Here is a summary of ways @conathan@ thought of to improve
-- BBVI. Only the first, simplest observation has been implemented, by
-- 'iteratedBbvi'.
--
-- When running BBVI to learn goal values @lambda@ that
-- are very far from the randomly chosen start values for
-- @lambda@, simply rerunning BBVI, starting from the previous
-- @lambda@, works well. For example, in
--
-- > runBbviTestUsingLazyRand 1
-- >   2      {- singleFactorBbvi2 -}
-- >   3      {- bbviTest3 -}
-- >   0.01   {- epsilon -}
-- >   100    {- num trials -}
-- >   [ 1000 {- mu -}
-- >   , 10 ] {- sigma -}
--
-- when lambda is initialized via
--
-- > replicateM 2 $ distSample (Normal 0 10)
--
-- the guesses are likely to be close to zero and far from 1000,
-- the goal value for @mu@.
--
-- The goal is to learn @lambda = [1000,10]@, and starting with
-- random lambda near zero, and then redefining @sampleLambda@ to
-- return the result, and iterating, we get the following sequence
-- of discovered lambda values:
--
-- @
-- sampleLambda = return $
--   -- [266.51484560478195,7.379162331856864]
--   -- [484.67445818993525,7.68279736309357]
--   -- [695.344938596016,8.239851183556492]
--   -- [874.483037696744,9.262297809983037]
--   -- [976.4159168688128,9.889695342218715]
--   -- [999.2564614475032,10.024071543947]
--   -- [999.9992140408281,9.999553691817553]
--   [999.99991729097,10.000438169812853]
-- @
--
-- As the result gets closer to the correct answer @[1000,10]@,
-- the incremental BBVI calls converge much more quickly. So, the
-- above corresponds to 8 runs of BBVI, but only take 3 or 4 times
-- as long as the first run.
--
-- With this improvement via iteration in mind, an obvious idea is
-- to simply implement a meta algorithm that does this iteration
-- for us: run BBVI in a loop, reusing the last @lambda@ to seed
-- the current run, until the @lambda@ computed by this meta
-- algorithm stabilizes (or some number of iterations are reached,
-- since for some functions, e.g. @sin@-like functions, we would
-- never converge).
--
-- And why does this meta algorithm work? Because when we restart
-- BBVI the learning rate / step size is large again, so we can
-- make lots of early progress before the decreasing learning rate
-- artificially slows us down.
--
-- This observation motivates a more general approach/goal: how
-- can we adjust the learning rate in a more intelligent way, so
-- that we don't slow down too early, but do slow down when we
-- reach a local optimum? ("Get while the gettin' is good" and
-- then stop.)
--
-- First, some ideas for detecting that we're not making progress
-- anymore:
--
-- 1. the difference between two consecutive values of lambda is
--    small. This is the approach the BBVI paper suggests. As
--    we've seen, it's misleading in conjunction with the
--    decreasing learning rates suggested by the paper.
--
-- 2. a whole group (tail of the sequence of lambdas) is
--    "clustered". The work here is defining "clustered". For
--    example, if the average distance (or max distance) between a
--    bunch of lambdas was close to the min distance (or average
--    distance), then the points are clustered.
--
-- 3.  the value of the objective function (ELBO) is not increasing
--     fast enough / in proportion to the effort. The work here
--     includes
--
--     - evaluating / estimating the objective function: turns out
--       this is quite similar to estimating the gradient of the
--       objective, and using a control variate should be similar
--       here. Indeed, we can define a control variate by adding a
--       multiple of the score function (as we do for estimating the
--       gradient itself.
--
--     - defining "fast enough / in proportion to the effort". For
--       example, we could define a "velocity of improvement" as the
--       ratio of the change in the objective to the step size.
--
-- Second, some ideas for ensuring we do keep making progress when
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
--
-- So, there are a lot of interesting things we could try ...

-- | The type of BBVI algorithms.
--
-- The @m@ is always monadic, but adding a @Monad m@ constraint on the
-- RHS here causes problems with "impredicative polymorphism" later,
-- when we try to make a list of @Bbvi m a@.
type Bbvi m a =
  R {-^ @epsilon@  -} ->
  Int {-^ @numSamples@ -} ->
  (Int -> [R] -> [R]) {-^ @projectLambda@ -} ->
  m [R] {-^ @sampleLambda@ -} ->
  ([R] -> m a) {-^ @sampleQ@  -} ->
  (a -> [R] -> m R) {-^ @evalLogQ@ -} ->
  (a -> [R] -> m [R]) {-^ @evalGradLoqQ@ -} ->
  (a -> m R) {-^ @evalLogP@ -} ->
  m [R]

-- | Black Box Variational Inference Algorithm 1.
--
-- From
-- http://www.cs.columbia.edu/~blei/papers/RanganathGerrishBlei2014.pdf.
--
-- We assume that @evalLogP@ is already (partially) applied to the
-- data @x@, unlike in the paper.
--
-- Here @epsilon@ is @0.01@ in the paper, and @numSamples@ is the
-- unspecified @S@ in the paper.
--
-- The @projectLambda@ function is used to project computed @lambda@
-- values back into the valid range of values for lambda.
--
-- === /Alternative approach/
--
-- As an alternative to defining a non-identity @projectLambda@, you
-- can "just" reparameterize to make @lambda@ range over all of
-- @R^n@. This is complicated and not suggested; see `bbviTest2` for
-- an example of reparameterizing.
--
-- You may be able to use functions from our 'Continuous' class to do
-- the transformations.
--
-- For example, normal distributions only support positive values for
-- sigma; we can work around this by using @fromRealLbInfty 0@ and
-- @toRealLbInfty 0@.
--
-- Alternatively, it might be possible to make the @q@-related
-- functions signal some kind of error when some part of lambda is out
-- of range. Not sure how to best recover here, but coming up with a
-- good way to recover could be much simpler than reparameterizing.
bbvi1 :: Monad m => Bbvi m a
bbvi1 epsilon numSamples projectLambda
  sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP = do
  lambda <- projectLambda 1 <$> sampleLambda
  loop lambda 1
  where
    loop lambda t = do
      zs <- replicateM numSamples (sampleQ lambda)
      elboGradTerms <- forM zs $ \z -> do
        glq <- evalGradLogQ z lambda
        lq <- evalLogQ z lambda
        lp <- evalLogP z
        return $ (lp - lq) `scaleV` glq
      let elboGrad = (1 / fromIntegral numSamples) `scaleV`
                     sumV elboGradTerms
      let lambda' = projectLambda t $ lambda `addV` (rho t `scaleV` elboGrad)
      let delta = ell1 $ lambda `subV` lambda'
      if delta >= epsilon
      then loop lambda' (t + 1)
      else trace ("t = "++show t) $ return lambda'

    -- Paper says any sequence converging in @\ell^2@ and diverging in
    -- @\ell^1@ will do for @rho@ here.
    rho t = 1/fromIntegral t

-- | Single factor Black Box Variational Inference Algorithm 2,.
--
-- The n-factor algorithm can be implemented in terms of the single
-- factor algorithm, assuming the factors can be sampled
-- independently, which seems likely since their pdfs are independent
-- by assumption. The single factor Algorithm 2 is pretty similar to
-- Algorithm 1, except we use control variates to reduce the
-- variation.
--
-- See 'bbvi1' for more docs.
--
-- The use of @projectLambda@ in this implementation only corresponds
-- to the AdaGrad paper when the domain of lambda is a closed (hyper)
-- rectangle, but (partially) open rectangles should be close
-- enough. For non-rectangular domains, the projection function in the
-- AdaGrad paper takes @diagG@ into account via a "Mahalanobis norm"
-- (same as the @\ell^2@ norm for rectangular domains in this
-- context). I expect this doesn't matter much ...
--
-- TODO: change this into a stream algorithm, so that epsilon does not
-- have to be passed in, and instead the caller can just
--
-- > dropWhile (error > epsilon)
--
-- Chad suggested this approach earlier for coordinate descent.
singleFactorBbvi2 :: Monad m => Bbvi m a
singleFactorBbvi2 epsilon numSamples projectLambda
  sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP = do
  lambda <- projectLambda 1 <$> sampleLambda
  let diagG = map (const 0) lambda
  loop diagG lambda 1
  where
    loop diagG lambda t = do
      zs <- replicateM numSamples (sampleQ lambda)
      hs <- forM zs $ \z -> do
        evalGradLogQ z lambda
      fs <- forM (zip zs hs) $ \(z, h) -> do
        lq <- evalLogQ z lambda
        lp <- evalLogP z
        return $ (lp - lq) `scaleV` h

      -- In the paper they say that they used 1000 for @numSamples@
      -- (called @S@ in the paper) and 100 estimates (i.e. 1/10th of
      -- the 1000) for the approximate Cov and Var in the computation
      -- of @\hat{a}^*_d@. So, we're generalizing this to using 1/10th
      -- of the samples.
      let numSamples' = if numSamples <= 10
                        then numSamples
                        else numSamples `div` 10
      let hs' = take numSamples' hs
      let fs' = take numSamples' fs
      let hs't = transpose hs'
      let fs't = transpose fs'
      let as = [ cov fCol hCol / var hCol | fCol <- fs't | hCol <- hs't ]

      let elboGradTerms = [ f `subV` aH
                          | f <- fs
                          | aH <- map (multV as) hs ]
      let elboGrad = (1 / fromIntegral numSamples) `scaleV` sumV elboGradTerms
      let diagG' = diagG `addV` (elboGrad `multV` elboGrad)
      -- Square root of pseudo inverse of @diagG'@.
      let learningRate = eta `scaleV`
                         [ if x == 0 then 0 else x**(-0.5) | x <- diagG' ]
      let dLambda = learningRate `multV` elboGrad
      let lambda' = projectLambda t $ lambda `addV` dLambda

      let delta = ell1 $ lambda `subV` lambda'
      if trace ("delta = "++show delta++"\ndiagG = "++show diagG'++"\ndLambda = "++show dLambda++"\nlambda = "++show lambda') $
         delta >= epsilon
      then loop diagG' lambda' (t + 1)
      else trace ("t = "++show t) $ return lambda'

    -- I think the AdaGrad paper said this parameter doesn't matter
    -- much (e.g. the theorem about the regret going to zero doesn't
    -- depend on an optimal choice for eta). I think this is the value
    -- they used though.
    eta = 2**0.5

    -- Note that @cov@ and @var@ are unnormalized -- i.e. not divided
    -- by the length of the input vectors -- since the normalization
    -- factors would just cancel in the calculation of @as@ as a ratio
    -- of @cov@ to @var@.
    var xs = cov xs xs
    cov xs ys = sum [ (x - meanXs) * (y - meanYs) | x <- xs | y <- ys ]
      where
        meanXs = mean xs
        meanYs = mean ys
    mean xs = sum xs / fromIntegral (length xs)

-- | Iterate BBVI until convergence or round limit is reached.
--
-- The @bbvi@ argument is expected to be a partially applied to all
-- arguments except for @sampleLambda@.
iterateBbvi ::
  Monad m =>
  Int ->
  R ->
  m [R] ->
  (m [R] -> m [R]) ->
  m [R]
iterateBbvi maxRounds epsilon sampleLambda bbvi = do
  result <- bbvi sampleLambda
  go 2 result
  where
    go round result
      | round >= maxRounds = return result
      | otherwise = do
          result' <- bbvi (return result)
          if ell1 (result `subV` result') <= epsilon
            then return result'
            else trace (show result') $ go (round + 1) result'

-- | Create an iterated version of an existing BBVI algorithm.
--
-- A helper to call @iterateBbvi@ for you, producing something of type
-- @Bbvi@' (useful for tests where I want to put BBVI algs in a list).
iteratedBbvi :: Monad m => Int -> Bbvi m a -> Bbvi m a
iteratedBbvi maxRounds bbvi epsilon numSamples projectLambda
  sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP =
  iterateBbvi maxRounds epsilon sampleLambda
  (\sample -> bbvi epsilon numSamples projectLambda
              sample sampleQ evalLogQ evalGradLogQ evalLogP)

-- | A variety of BBVI algs for use in testing.
bbvis :: Monad m => [Bbvi m a]
bbvis =  [ bbvi1
         , singleFactorBbvi2
         , iteratedBbvi 100 bbvi1
         , iteratedBbvi 100 singleFactorBbvi2 ]

----------------------------------------------------------------
-- * Variational families
----------------------------------------------------------------
--
-- $variationalFamilies
-- The code needed to use a specific variational family (the @q \in
-- Q@) with a BBVI algorithm is independent of the target distribution
-- (the @p@) being approximated.

----------------------------------------------------------------
-- ** Normal

sampleNormal :: SampleableIn m Normal => [R] -> m R
sampleNormal [mu, sigma] = distSample (Normal mu sigma)

evalLogNormalDensity :: Monad m => R -> [R] -> m R
evalLogNormalDensity z [mu, sigma] = return $
  probToLogR $ distDensity (Normal mu sigma) z

evalGradLogNormalDensity :: Monad m => R -> [R] -> m [R]
evalGradLogNormalDensity z [mu, sigma] = return
  -- Calculated by hand from @normalDensity@ ...
  [ (z - mu) / sigma
  , (z - mu)**2 / sigma**3 - 1 / sigma ]

projectLambdaNormal :: Int -> [R] -> [R]
projectLambdaNormal = projectRectangle
  [ (OpenBound (-1/0), OpenBound (1/0)),
    (OpenBound 0, OpenBound (1/0)) ]

----------------------------------------------------------------
-- ** Multivariate normal
--
-- $mvNormal
-- Everywhere below @k@ is the dimension of the mv normal.

-- | Convert the flat list of params used by the bbvi algorithm into
-- the vector and matrix params used by the mv normal distribution.
paramsToDistParamsMVNormal :: Int -> [Double] -> (Vector Double, Matrix Double)
paramsToDistParamsMVNormal k muAndC =
  if length muAndC /= expectedLength
  then error $
       "paramsToDistParamsMVNormal: "++
       "the parameter list is the wrong length! Expected: "++
       show expectedLength++", actual: "++show (length muAndC)
  else (mu, c)
  where
    -- An upper triangular @k x k@ matrix has @k + 1@ choose 2
    -- potentially non-zero entries.
    expectedLength = k + ((k * (k+1)) `div` 2)

    (muList, cList) = splitAt k muAndC
    mu = La.fromList muList
    c = (k La.>< k) $ upperTriangular k cList

-- | Build full list of entries in upper triangular matrix from list
-- of its potentially non-zero entries.
--
-- Builds up the full list for the matrix by filling in zeros for
-- undefined entries. The undefined entries are the lower tringular,
-- i.e. where the row index is larger than the column index.
upperTriangular :: (Num a) => Int -> [a] -> [a]
upperTriangular k xs0 = zeroPad rcs xs0
  where
    rcs = [ (r, c) | r <- [0..(k-1)], c <- [0..(k-1)] ]
    zeroPad []           []         = []
    zeroPad ((r,c):rcs') xs@(x:xs') =
      if r > c
      then 0 : zeroPad rcs' xs
      else x : zeroPad rcs' xs'

sampleMVNormal :: SampleableIn m MVNormal => Int -> [R] -> m (Vector R)
sampleMVNormal k muAndC = distSample (MVNormal mu c)
  where
    (mu, c) = paramsToDistParamsMVNormal k muAndC

-- | The @k@ is the dimension of the mv normal.
evalLogMVNormalDensity ::
  Monad m => Int -> Vector R -> [R] -> m R
evalLogMVNormalDensity k z muAndC = return $
  probToLogR $ distDensity (MVNormal mu c) z
  where
    (mu, c) = paramsToDistParamsMVNormal k muAndC

-- | The log pdf is
--
-- > lpdf = -1/2 ( ln |C^T C| + (x-mu)^T(C^T C)^{-1}(x-mu) + k ln (2 pi) ) ,
--
-- where @|M|@ is the absolute value of the determinant of @M@.
--
-- The partials with respect to @mu@'s components are easy. The
-- product rule gives
--
-- > d_{mu_i} lpdf = -1/2 ( m^T(C^T C)^{-1}(x-mu) + (x-mu)^T(C^T C)^{-1}m )
--
-- for @m := - d_{mu_i} mu@, i.e. a vector with @m_j = - (Kronecker) delta i j@.
--
-- The partials with respect to @C@'s components are trickier, but
-- simplified by the fact that the determinant of @C@ is simple.
--
-- Let @d@ be some partial @d/dC_{ij}@. It comes down to calculating
--
-- > d ln |C^T C|
--
-- and
--
-- > d (x-mu)^T(C^T C)^{-1}(x-mu) .
--
--
-- For the first term we have @|C^T C|@ = @|C|^2@ and so
--
-- > ln |C^T C| = 2 ln |C|
--
-- and so
--
-- > d ln |C^T C| = (2/|C|) d |C| .
--
-- Since @C@ is upper triangular with positive diagonal, we have
--
-- > |C| = C_{11} .. C_{kk}
--
-- and so for @d = d/dC_{ij}@ we have
--
-- > d |C| = if i == j then |C|/C_{ij} else 0 .
--
-- and so
--
-- > d ln |C^T C| = if i == j then 2/C_{ij} else 0 .
--
--
-- For the second term we have
--
-- > (C^T C)^{-1} = (C^{-1}) (C^{-1})^T
--
-- and so
--
-- > d (C^T C)^{-1} = (d C^{-1}) (C^{-1})^T + C^{-1} (d C^{-1})^T ,
--
-- and so we just need the derivative of the inverse:
--
-- > d C^{-1} = - C^{-1} (d C) C^{-1}
--
-- see http://planetmath.org/derivativeofinversematrix.
--
-- Putting that all back together, with @B := C^{-1}@, we have
--
-- > d (C^T C)^{-1} = - (B dC B B^T + B B^T dC^T B^T)
-- >                = - B (dC B + (dC B)^T) B^T
--
-- and for @d = d/d(C_{ij})@ we have
--
-- > (dC)_{st} = delta i s * delta j t .
evalGradLogMVNormalDensity ::
  Monad m => Int -> Vector Double -> [R] -> m [R]
evalGradLogMVNormalDensity k x muAndC =
  return $ map (* (-1/2)) $ muGrads ++ cGrads
  where
    (mu, c) = paramsToDistParamsMVNormal k muAndC
    delta i j = if i == j then 1 else 0

    muGrads = [ d <.> cInvFun (x - mu) +
                (x - mu) <.> cInvFun d
              | i <- [ 0 .. k-1 ]
              , d <- [ La.fromList $ map (((-1) *) . delta i) [ 0 .. k-1 ] ] ]
    -- Efficient left multiplication of a vector by @(C^T C)^{-1}@.
    cInvFun = La.flatten . La.cholSolve c . La.asColumn

    cGrads = [ lnGrad i j + prodGrad i j
             | i <- [ 0 .. k-1 ]
             , j <- [ i .. k-1 ] ]
    lnGrad i j = if i == j then 2 / (c `La.atIndex` (i, j)) else 0
    prodGrad i j = (x - mu) <.> middle #> (x - mu)
      where
        middle = (-1) * b <> (dC i j <> b + La.tr (dC i j <> b)) <> La.tr b
    -- The inverse of @C@ as a matrix.
    (b, _) = La.invlndet c
    -- The derivative of @C@ w.r.t. @C_{ij}@.
    dC i j = La.assoc (k, k) 0 [ ((i, j), 1) ]

-- | The diagonal entries of the Cholesky matrix must be positive. The
-- other values are unconstrained.
--
-- The @k@ is the dimension of the mv normal.
projectLambdaMVNormal :: Int -> Int -> [R] -> [R]
projectLambdaMVNormal k = projectRectangle $ muBounds ++ cBounds
  where
    reals = (OpenBound (-1/0), OpenBound (1/0))
    positiveReals = (OpenBound 0, OpenBound (1/0))

    muBounds = replicate k reals
    cBounds = flip concatMap [ k, k - 1 .. 1 ] $ \rowLength ->
      take rowLength $ [ positiveReals ] ++ repeat reals

----------------------------------------------------------------
-- *** Test mv normal implementation.
--
-- $testMvNormal
--
-- The gradient we calculated by hand was quite complicated, so
-- compare it with the gradient we get from automatic differentiation
-- (would have been much faster in human time to just use automatic
-- differentiation in the first place, but now we have very high
-- confidence the gradient is correct).

-- | An overloaded (i.e. @Floating@) implementation of the log pdf.
--
-- This allows us to use automatic differentiation and compare the
-- result with the manual, by hand gradient
-- 'evalGradLogMVNormalDensity' above.
logMVNormalDensityOverloaded ::
  (Floating a, Eq a) => Int -> [a] -> [a] -> a
logMVNormalDensityOverloaded k xList muAndC =
  ((- 0.5) *) $
  2 * log detC +
  fromIntegral k * log (2 * pi) +
  -- The @Dm@ library uses 1-based indexing.
  prod Dm.! (1,1)
  where
    (muList, cList) = splitAt k muAndC
    x = Dm.fromList k 1 xList
    mu = Dm.fromList k 1 muList
    c = Dm.fromList k k $ upperTriangular k cList
    detC = foldr (*) 1 $ Dm.getDiag c
    sigma = Dm.transpose c * c
    Right sigmaInv = Dm.inverse sigma
    prod = (Dm.transpose $ x - mu) * sigmaInv * (x - mu)

-- | Use automatic differentiation to check the manually computed mv
-- normal gradient.
compareGrads :: Monad m => Int -> [R] -> [R] -> m [R]
compareGrads k x muAndC = do
  manual <- evalGradLogMVNormalDensity k (La.fromList x) muAndC
  -- AD needs the function to differentiate to overloaded / take
  -- @Floating@ arguments.
  let x' :: Floating a => [a]
      x' = map (fromRational . toRational) x
  let auto = Ad.grad (logMVNormalDensityOverloaded k x') muAndC
  -- The rescaling of errors is essential here: without it, for very
  -- large gradient entries (e.g. size 10^10), there can be large
  -- absolute differences between gradient entries. We care about
  -- large relative differences, which can't be explained away by
  -- rounding error. Dividing by 1 here avoids division by zero, and
  -- means we avoid spurious differences detected when we divide by
  -- very small numbers.
  return $ [ abs (m - a) / (abs m + abs a + 1) | m <- manual | a <- auto ]

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

    i :: [Integer] -> [R]
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

----------------------------------------------------------------
-- * Tests
----------------------------------------------------------------

-- | Even simpler version of the 'bbv1Test2' below.
--
-- Here we approximate a normal by a normal. The standard deviation is
-- fixed, and we fit the mean. The input @mu@ and @sigma@ are the
-- parameters of the normal that we are trying to approximate; our
-- goal is to discover @mu@.
--
-- We make @mu@ the parameter to discover, because it ranges over all
-- reals and so no transformations are needed.
--
-- Returns the error in the discovered @mu@, and the discovered @mu@.
bbviTest1 ::
  (SampleableIn m Normal) =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest1 algNum epsilon numSamples [mu, sigma] = do
  [mu'] <- (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
           sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP
  let error' = ell1 $ [mu'] `subV` [mu]
  return (error', [mu'])
  where
    -- We can see that bbvi1 at least kind of works by seeding @lambda@
    -- with a value very close to the right answer.
    --
    -- sampleLambda = replicateM 1 $ distSample (Normal mu 0.1)
    sampleLambda = defaultSampleLambda 1
    sampleQ [mu'] = distSample (Normal mu' sigma)
    evalLogQ z [mu'] = return $
      probToLogR $ distDensity (Normal mu' sigma) z
    evalGradLogQ z [mu'] = return [ (z - mu') / sigma ]
    evalLogP z = return $
      probToLogR $ distDensity (Normal mu sigma) z
    projectLambda _ lambda = lambda

-- | Test 'bbv1' by approximating a linear combination of normals by a
-- normal ... except it turns out that a linear combination of normals
-- *is* a normal, and the only way to analytically weight its samples
-- is to know this, so I'm really just going to approximate a normal
-- by a normal. At least we can expect this to succeed :D
--
-- Formulas for linear combination of normals are here:
-- https://www.statlect.com/probability-distributions/normal-distribution-linear-combinations.
--
-- Note that we have to transform the standard deviation param sigma,
-- per the comments above in 'bbvi1'.
bbviTest2 ::
  (SampleableIn m Normal) =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest2 algNum epsilon numSamples [mu, sigma] = do
  [mu', sigma'] <- fRLambda <$>
    (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
    sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP
  -- In general, it might only make sense to compute the error in the
  -- real domain.
  let error' = ell1 $ [mu', sigma'] `subV` [mu, sigma]
  return (error', [mu', sigma'])
  where
    projectLambda _ lambda = lambda
    -- Since lambda is always a vector of reals, it's not clear why it
    -- should be a param to 'bbvi1'.
    --
    -- !!!: THE @fromRealLbInfty 0@ UNDERFLOWS TO ZERO FOR LARGE VALUES.
    --
    -- ???: does the delta in the output change when we increase
    -- numSampls???
    sampleLambda = defaultSampleLambda 2

    sampleQOrig = sampleNormal
    sampleQ = sampleQOrig . fRLambda

    evalLogQOrig = evalLogNormalDensity
    evalLogQ z = evalLogQOrig z . fRLambda

    -- Calculated by hand from @normalDensity@ ...
    evalGradLogQOrig = evalGradLogNormalDensity
    evalGradLogQ z lambda =
      -- Chain rule specialized to vars transformed independently
      -- (i.e. the derivative matrix of the transformation @fRLambda@
      -- is diagonal).
      zipWith (*) (fRLambda' lambda) <$>
      evalGradLogQOrig z (fRLambda lambda)

    evalLogP z = evalLogNormalDensity z [mu, sigma]

    -- Transformations from and to reals for sigma param of
    -- normal. Note: the 'Continuous' class transforms the support /
    -- output, not the params / input of a distribution.
    fRSigma = fromRealLbInfty 0
    fRSigma' = probToR . fromRealLbInfty' 0
    -- tRSigma = toRealLbInfty 0

    fRLambda [mu', sigma'R] = [mu', fRSigma sigma'R]
    -- Here @1@ is the derivative of the identity.
    fRLambda' [_mu', sigma'R] = [1, fRSigma' sigma'R]
    -- tRLambda [mu', sigma'] = [mu', tRSigma sigma']

-- | Like `bbviTest2`, but use a non-trivial `projectLambda`, instead
-- of a reparameterization.
bbviTest3 ::
  (SampleableIn m Normal) =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest3 algNum epsilon numSamples [mu, sigma] = do
  [mu', sigma'] <-
    (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
    sampleLambda sampleQOrig evalLogQOrig evalGradLogQOrig evalLogP
  -- In general, it might only make sense to compute the error in the
  -- real domain.
  let error' = ell1 $ [mu', sigma'] `subV` [mu, sigma]
  return (error', [mu', sigma'])
  where
    -- Since lambda is always a vector of reals, it's not clear why it
    -- should be a param to 'bbvi1'.
    --
    -- !!!: THE @fromRealLbInfty 0@ UNDERFLOWS TO ZERO FOR LARGE VALUES.
    sampleLambda = defaultSampleLambda 2
    sampleQOrig = sampleNormal
    evalLogQOrig = evalLogNormalDensity
    evalGradLogQOrig = evalGradLogNormalDensity
    projectLambda = projectLambdaNormal

    evalLogP z = evalLogNormalDensity z [mu, sigma]

-- | Learn a normal that approximates a Student's t-distribution.
--
-- The parameters are @mu@ real and @nu@ positive real.
--
-- We want the mean of the learned normal to be the mean of the
-- t-distribution. I don't know what to expect for the std deviation
-- of the learned normal tho. The variance of the t-distribution is
-- @nu / (nu - 2)@ for @nu > 2@ and infinite or undefined otherwise.
--
-- See https://en.wikipedia.org/wiki/Student's_t-distribution.
bbviTest4 ::
  SampleableIn m Normal =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest4 algNum epsilon numSamples [mu, nu] = do
  [mu', sigma'] <-
    (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
    sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP
  -- In general, it might only make sense to compute the error in the
  -- real domain.
  let error' = ell1 $ [mu'] `subV` [mu]
  return (error', [mu', sigma'])
  where
    sampleQ = sampleNormal
    evalLogQ = evalLogNormalDensity
    evalGradLogQ = evalGradLogNormalDensity
    sampleLambda = defaultSampleLambda 2
    projectLambda = projectLambdaNormal

    evalLogP z = return $
      S.logDensity (S.studentT nu) (z - mu)

----------------------------------------------------------------

-- | Learn a multivariate normal that approximates a linear
-- regression.
--
-- The linear regression has parameters slope @m@, @y@-intercept @b@,
-- and error standard deviation @sigma@. The generative model
-- comprises a arbitrary distribution of the parameters @m@, @b@, and
-- @sigma@, say
--
-- > m ~ Uniform 0 10
-- > b ~ Uniform 0 10
-- > sigma ~ Uniform 0 10 ,
--
-- and a noisy linear distribution on the dependent variable @y@ given
-- the independent variable @x@, i.e.
--
-- > e ~ Normal 0 sigma
-- > y := m*x + b + e ,
--
-- or equivalently
--
-- > y ~ Normal (m*x + b) e .
--
-- So, the joint distribution given data
--
-- > xys = [(x1,y1),...,(xn,yn)]
--
-- is
--
-- > P[xys,m,b,sigma] = P[xys|m,b,sigma] * P[m,b,sigma] ,
--
-- where
--
-- > P[m,b,sigma] = 1
--
-- and
--
-- > P[xys|m,b,sigma] = p(x1,y1) * ... * p(xn,yn) ,
--
-- for
--
-- > p(x,y) =
-- > Pr[y = m*x + b + e] =
-- > Pr[e = y - m*x - b] =
-- > distDensity (Normal (m*x + b) sigma) y .
--
-- The @xysFlat@ argument is
--
-- > [x1,y1,x2,y2,...,xn,yn] .
bbviTest5 ::
  (SampleableIn m Normal, SampleableIn m MVNormal) =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest5 algNum epsilon numSamples (m:b:sigma:xysFlat) = do
  muAndC'@(m':b':sigma':_cList') <-
    (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
    sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP
  let error' = ell1 $ [m',b',sigma'] `subV` [m,b,sigma]
  return (error', muAndC')
  where
    -- Three dimensions, for @m@, @b@, and @sigma@.
    k = 3
    muSize = k
    cSize = (k * (k+1)) `div` 2

    sampleQ = sampleMVNormal k
    evalLogQ = evalLogMVNormalDensity k
    evalGradLogQ = evalGradLogMVNormalDensity k
    sampleLambda = defaultSampleLambda (muSize + cSize)
    projectLambda = projectLambdaMVNormal k

    xys = go xysFlat
      where
        go [] = []
        go (x:y:xysFlat') = (x,y) : go xysFlat'

    evalLogP mBSigma = return $ linRegLogDensity xys m' b' sigma'
      where
        [m', b', sigma'] = La.toList mBSigma

-- | A version of 'bbviTest5' that fixes the noise deviation sigma, so
-- that the mv normal only needs two params. The sigma passed in will
-- be used, and should correspond to the supplied data in @xysFlat@.
bbviTest7 ::
  (SampleableIn m Normal, SampleableIn m MVNormal) =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest7 algNum epsilon numSamples (m:b:sigma:xysFlat) = do
  muAndC'@(m':b':_cList') <-
    (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
    sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP
  let error' = ell1 $ [m',b'] `subV` [m,b]
  return (error', muAndC')
  where
    -- Two dimensions, for @m@, @b@.
    k = 2
    muSize = k
    cSize = (k * (k+1)) `div` 2

    sampleQ = sampleMVNormal k
    evalLogQ = evalLogMVNormalDensity k
    evalGradLogQ = evalGradLogMVNormalDensity k
    sampleLambda = defaultSampleLambda (muSize + cSize)
    projectLambda = projectLambdaMVNormal k

    xys = go xysFlat
      where
        go [] = []
        go (x:y:xysFlat') = (x,y) : go xysFlat'

    evalLogP mB = return $ linRegLogDensity xys m' b' sigma
      where
        [m', b'] = La.toList mB

linRegLogDensity ::
  [(R, R)] -> R -> R -> R -> R
linRegLogDensity xys m b sigma =
  -- An alternative approach:
  --
  -- The @abs sigma'@ is here to avoid using negative sigma
  -- values. Not sure what the right approach is here: we could
  -- use a different @projectLambda@ implementation that restricts
  -- to positive third component (i.e. the mean of the sigma
  -- values), but that won't stop them from being
  -- negative.
  {-
  sum [ logFromLogFloat (distDensity (Normal (m'*x + b') (abs sigma')) y)
      | (x, y) <- xys ]
  -}
  -- We penalize negative sigmas, by returning a very small value
  -- here.
  if sigma > 0
  then
    (if logProb < logVerySmallValue
     then trace ("XXX: logProb is very small: "++show logProb)
     else id)
    logProb
  else
    -- Is this value is really small enough? Could try @-1/0@.
    --
    -- Update: using negative infinity, or more generally very large
    -- negative values here, causes various crashes (for finite values
    -- an underflow in @LogFloat@, and for negative infinity a
    -- malformed Cholesky factor).
    logVerySmallValue
    where
      logVerySmallValue = -10e10
      logProb = sum [ probToLogR $ distDensity (Normal (m*x + b) sigma) y
                    | (x, y) <- xys ]

simpleLinRegData :: Int -> R -> R -> [(R, R)]
simpleLinRegData numPoints m b =
  [ (x, m*x+b) | x <- [ 1 .. fromIntegral numPoints ] ]

genLinRegDataIO :: Int -> R -> R -> R -> IO [(R, R)]
genLinRegDataIO numSamples m b sigma = do
  g <- MWC.create
  runRand g $ genLinRegData numSamples m b sigma

genLinRegData ::
  ( SampleableIn m Normal, SampleableIn m Uniform ) =>
  Int -> R -> R -> R -> m [(R, R)]
genLinRegData numSamples m b sigma = do
  replicateM numSamples $ do
    -- Use integral @x@s to make the output a little easier to inspect
    -- visually.
    x <- fromInteger . round <$> distSample (Uniform (-1000) 1000)
    y <- distSample (Normal (m*x + b) sigma)
    return (x,y)

-- scatterPlot :: [(R, R)] -> ???
-- | Based on http://indiana.edu/~ppaml/HakaruTutorial.html and
-- https://github.com/timbod7/haskell-chart/wiki/example%202.
--
-- Writes output to an SVG file, regardless of supplied file extension
-- :P The examples I referred to use the Cairo backend, but I'm using
-- the Diagrams backend, so that might be the issue. So, I changed
-- this function to supply the extension, to avoid confusion.
scatterPlot :: String -> String -> [(R, R)] -> IO (G.PickFn ())
scatterPlot title file xys =
  G.renderableToFile G.def (file++".svg") $ G.toRenderable layout
  where
    plot = G.plot_points_style .~ G.filledCircles 2 (G.opaque G.purple)
           $ G.plot_points_values .~ xys
           $ G.def

    layout = G.layout_title .~ title
             $ G.layout_plots .~ [G.toPlot plot]
             $ G.layout_x_axis . G.laxis_generate .~ G.scaledAxis G.def (-4, 4)
             $ G.layout_y_axis . G.laxis_generate .~ G.scaledAxis G.def (-4, 4)
             $ G.def

-- | https://en.wikipedia.org/wiki/File:MultivariateNormal.png
--
-- I can't figure out how to set the aspect ratio :P
wikipediaExample :: IO ()
wikipediaExample = do
  g <- MWC.create
  xyVectors <- runRand g $ replicateM numSamples (distSample (MVNormal mu c))
  let xys = [ (x, y) | v <- xyVectors, [x,y] <- [ La.toList v ] ]
  _ <- scatterPlot ("Wikipedia Test ("++show numSamples++" samples)") "/tmp/out" xys
  return ()
  where
    mu = La.fromList [0, 0]
    c = La.chol (La.trustSym $ (2 La.>< 2) [1, 0.6, 0.6, 2])
    numSamples = 10000

----------------------------------------------------------------

-- | Sanity test: match an mv normal to an mv normal.
--
-- This works pretty well with iterated bbvi 2, e.g. with
--
-- > runBbviTestUsingLazyRand 1 4 6 1 1000 [1,2,3,1,0,0,2,0,3]
--
-- Of course, this doesn't prove much.
bbviTest6 ::
  (SampleableIn m Normal, SampleableIn m MVNormal) =>
  Int -> R -> Int -> [R] -> m (R, [R])
bbviTest6 algNum epsilon numSamples muAndC = do
  muAndC' <-
    (bbvis !! (algNum - 1)) epsilon numSamples projectLambda
    sampleLambda sampleQ evalLogQ evalGradLogQ evalLogP
  let error' = ell1 $ muAndC' `subV` muAndC
  return (error', muAndC')
  where
    k = 3
    muSize = k
    cSize = (k * (k+1)) `div` 2

    sampleQ = sampleMVNormal k
    evalLogQ = evalLogMVNormalDensity k
    evalGradLogQ = evalGradLogMVNormalDensity k
    sampleLambda = defaultSampleLambda (muSize + cSize)
    projectLambda = projectLambdaMVNormal k

    evalLogP z = evalLogMVNormalDensity k z muAndC

----------------------------------------------------------------

runBbviTestUsingLazyRand ::
  Int -> Int -> Int -> R -> Int -> [R] -> IO [(R, [R])]
runBbviTestUsingLazyRand numTrials algNum testNum epsilon numSamples testParams = do
  g <- MWC.create
  runRand g $ replicateM numTrials $ test algNum epsilon numSamples testParams
  where
    test = [ bbviTest1
           , bbviTest2
           , bbviTest3
           , bbviTest4
           , bbviTest5 -- Mv normal for linear regression: learn m, b, sigma.
           , bbviTest6 -- Mv normal for mv normal.
           , bbviTest7 -- Mv normal for linear regression: learn m, b.
           ] !! (testNum - 1)

test5 :: IO [(R, [R])]
test5 = runBbviTestUsingLazyRand 1 3 5 0.1 1000
  ([m,b,sigma] ++ concat [ [x, y] | (x, y) <- simpleLinRegData 1000 m b ])
  where
    m = 1
    b = 2
    sigma = 0.001
