{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds, PolyKinds, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Grappa.Distribution where

import Control.Monad
import Control.Monad.Trans
import GHC.Exts
import Data.Typeable
import Numeric.LinearAlgebra hiding (R, Uniform, (<>))
import qualified Data.Vector.Storable as V
--import Data.Number.LogFloat hiding (sum, product, log)

import qualified Numeric.Log as Log
import qualified Numeric.SpecFunctions as Gamma

import qualified Data.Matrix as M

import qualified Numeric.AD.Mode.Forward as ADF
import qualified Numeric.AD.Internal.Forward as ADF
import qualified Numeric.AD.Mode.Reverse as ADR
import qualified Numeric.AD.Internal.Reverse as ADR
import qualified Numeric.AD.Internal.Identity as ADR
import qualified Numeric.AD.Jacobian as ADR
import qualified Data.Reflection as ADR (Reifies)

-- | The R type alias
type R = Double

-- | The type of real-valued matrices
newtype RMatrix = RMatrix { unRMatrix :: M.Matrix Double }
                  deriving (Num,Eq)

-- | Grappa type for vectors
-- data Vec a

----------------------------------------------------------------------
-- * Supporting the Gamma and Beta Functions
----------------------------------------------------------------------

-- | Class for computing @ln (gamma x)@
class HasGamma a where
  logGamma :: a -> a
  digamma :: a -> a

instance HasGamma Double where
  logGamma = Gamma.logGamma
  digamma = Gamma.digamma

-- | The 'trigamma' function = the derivative of 'digamma' (which itself is the
-- derivative of 'logGamma'). This implementation was cribbed from
-- <https://stackoverflow.com/questions/2978979/how-to-improve-performance-of-this-numerical-computation-in-haskell/2983578 this>
-- Stack Overflow post
trigamma :: Double -> Double
trigamma x = go 0 (x + 5) $ computeP $ x + 6
  where
    go :: Int -> Double -> Double -> Double
    go !i !z !p
        | i >= 6    = p
        | otherwise = go (i+1) (z-1) (1 / (z*z) + p)
    invSq z = 1 / (z * z)
    computeP z = (((((5/66*p-1/30)*p+1/42)*p-1/30)*p+1/6)*p+1)/z+0.5*p
      where p = invSq z


----------------------------------------------------------------------
-- * Helper Definitions for Automatic Differentiation
----------------------------------------------------------------------

-- | Convert between two 'AD.Forward' types, using a conversion function which
-- should numerically be the identity, i.e., it should the representation of @r@
-- in type @a@ to the closest representable number to @r@ in @b@.
{-
unsafeConvertAD :: (a -> b) -> AD.Forward a -> AD.Forward b
unsafeConvertAD f (AD.Forward x y) =
  AD.Forward (f x) (f y)
unsafeConvertAD f (AD.Lift x) =
  AD.Lift (f x)
unsafeConvertAD _ AD.Zero = AD.Zero
-}

-- | Apply a function to an 'ADF.Forward' object that has a more efficient or
-- accurate version for the underlying type. For instance, log1p = log . (1+)
-- has a more accurate version in C code, but we still need to apply the above
-- mathematical definition to compute the derivative.
optimizedADOp :: Num a => (ADF.Forward a -> ADF.Forward a) -> (a -> a) ->
                 ADF.Forward a -> ADF.Forward a
optimizedADOp f f_opt x =
  ADF.bundle (f_opt $ ADF.primal x) (ADF.tangent $ f x)

-- Needed to use @'ADF.Forward' 'Double'@ Log
instance Log.Precise (ADF.Forward Double) where
  log1p = optimizedADOp Log.log1p (log . (1 +))
  expm1 = optimizedADOp Log.expm1 ((\x -> x - 1) . exp)

-- Needed to use @'ADR.Reverse' 'Double'@ Log
instance ADR.Reifies rs ADR.Tape => Log.Precise (ADR.Reverse rs Double) where
  log1p x = ADR.unary Log.log1p (ADR.Id (1 / (ADR.primal x + 1))) x
  expm1 x = ADR.unary Log.expm1 (ADR.Id ((ADR.primal x) * exp (ADR.primal x))) x

instance ADR.Reifies s ADR.Tape => HasGamma (ADR.Reverse s Double) where
  logGamma x =
    ADR.unary Gamma.logGamma (ADR.Id $ Gamma.digamma $ ADR.primal x) x
  digamma x =
    ADR.unary Gamma.logGamma (ADR.Id $ trigamma $ ADR.primal x) x


----------------------------------------------------------------------
-- * Probabilities
----------------------------------------------------------------------

-- | We use the shorthand @Prob@ for the type of probabilities
newtype Prob = Prob { fromProb :: Log.Log Double }
             deriving (Num,Eq,Ord,Real,Fractional,Typeable)

instance Show Prob where
  show (Prob x) = show x

-- | Specialized method for testing if a 'Prob' is zero
probIsZero :: Prob -> Bool
probIsZero (Prob x) = x == 0

-- | Specialized method for testing if a 'Prob' is a NaN
probIsNaN :: Prob -> Bool
probIsNaN (Prob x) = isNaN $ Log.ln x

-- | Convert a (non-negative) real to a 'Prob'
rToProb :: R -> Prob
rToProb = Prob . Log.Exp . log

-- | Convert a real that is already in log-space to a 'Prob'
logRToProb :: R -> Prob
logRToProb = Prob . Log.Exp

-- | Convert a 'Prob' to a real (not in log space)
probToR :: Prob -> R
probToR = exp . Log.ln . fromProb

-- | Convert a 'Prob' to a real in log space
probToLogR :: Prob -> R
probToLogR = Log.ln . fromProb

-- | Lifting the 'Log.sum' method to 'Prob'
sumProb :: [Prob] -> Prob
sumProb ps = Prob $ Log.sum $ map fromProb ps


----------------------------------------------------------------------
-- * Distributions
----------------------------------------------------------------------

-- | This defines the support type of a distribution
type family Support (d :: *) :: *

-- | The base class for distributions, stating that we can evaluate the density
-- of any given distribution at a particular value.  For debugging purposes, we
-- also require distributions to be 'Show'able.
class PDFDist d where
  distDensity :: d -> Support d -> Prob

-- | This type class states that monad @m@ supports distribution type @d@ by
-- allowing distributions of type @d@ to be randomly sampled in @m@
class Monad m => SampleableIn m d where
  distSample :: d -> m (Support d)

instance (SampleableIn m d,
          Monad (t m), MonadTrans t) => SampleableIn (t m) d where
  distSample = lift . distSample

-- | This type family states that all distribution types in @ds@ satisfy @c@
type family DistsIn (ds :: [*]) (c :: * -> Constraint) :: Constraint where
  DistsIn '[] c = ()
  DistsIn (d ': ds) c = (c d, DistsIn ds c)

-- | Type family that applies every constraint in a list to @a@
type family ApplyAll (cs :: [* -> Constraint]) (a :: *) :: Constraint where
  ApplyAll '[] a = ()
  ApplyAll ('(:) c cs) a = (c a, ApplyAll cs a)

-- | Type-class version of 'ApplyAll'
class ApplyAll cs a => All cs a
instance ApplyAll cs a => All cs a

-- | Type family that applies every constraint in a list to @a@
type family ReprApplyAll (cs :: [((* -> *) -> *) -> (* -> *) -> Constraint]) (d :: (* -> *) -> *) (a :: * -> *) :: Constraint where
  ReprApplyAll '[] d f = ()
  ReprApplyAll ('(:) c cs) d f = (c d f, ReprApplyAll cs d f)

-- | Type-class version of 'ApplyAll'
class ReprApplyAll cs d f => ReprAll cs d f
instance ReprApplyAll cs d f => ReprAll cs d f

-- | This constraint says that the distribution type @d@ is continuous, i.e.,
-- isomorphic to the reals.
--
-- The class functions take @d@, not @Proxy d@, since e.g. we need
-- different implementations for @uniform 0 1 :: Uniform@ and @uniform
-- 1 2 :: Uniform@.
class Continuous d where
  -- | Note that 'toReal' need not be defined on all of @Support d@,
  -- and implementation should raise an error on out of bounds
  -- values. E.g., for @uniform 0 1@, we have @Support Uniform ~
  -- R@, but in fact 'toReal' is only defined on @[0,1]@. We
  -- don't use @Maybe R@ as the return type, since passing an out
  -- of bounds value to 'toReal' is probably a bug.
  toReal :: d -> Support d -> R
  fromReal :: d -> Double -> Support d

{- FIXME: this does not seem to be the derivative in the below, and is in fact
just fromReal in log-space. Figure this out or remove it!

  -- | The derivative of 'fromReal'.
  --
  -- In the multivariable case the derivative becomes the determinant
  -- of the Jacobian (matrix of partial derivatives).
  --
  -- We can factor this into a separate class if we end up with some
  -- continuous distributions for which we don't have Jacobian
  -- determinants.
  fromReal' :: d -> Double -> LogFloat
-}

-- | The PDF of a continuous dist transformed to be a dist on the
-- whole real line.
--
-- All of our single variable transforms are increasing, so I don't
-- think we have to worry about taking absolute values; indeed, the
-- @LogFloat@ is not even defined for negative values. (compare
-- formulas for single dimensional change of variables which uses
-- derivative and multiple dimension change of variables where the
-- *absolute value* of the Jacobian is used:
-- https://en.wikipedia.org/wiki/Integration_by_substitution).
{-
fromRealDistDensity :: (Continuous d, PDFDist d) => d -> Double -> Prob
fromRealDistDensity d x = distDensity d (fromReal d x) * Prob (fromReal' d x)
-}

----------------------------------------------------------------
-- * Helper functions for defining 'Continuous' instances
----------------------------------------------------------------

-- TODO(conathan): revisit these bijections once we have a better
-- understanding of any additional properties we want from them. We
-- plan to use these bijections to work in the reals and not have to
-- worry about bounds.
--
-- Potential trouble: consider the open interval @(lb,ub)@ bijection
-- below in @toRealLbUb@ and @fromRealLbUb@. The logit function @\p ->
-- log (p / (1 - p))@ is small for most of the reals, so if we do
-- anything where we choose random reals over a large range, nearly
-- all of them will cluster in the ends of underlying interval
-- (i.e. near @lb@ and @ub@). If we want more uniform choices in the
-- reals to map to more uniform choices in our underlying interval,
-- then we'll need a bijection that spreads the interval much wider.
--
-- Some bijections to consider (these need to be scaled to work with
-- @(lb,ub)@):
--
-- - @\x -> log (x / (1 - x))@:
--   https://www.wolframalpha.com/input/?i=plot+log+(x+/+(1+-+x))
--
-- - @\x -> (1 / (1 - x)) - (1 / x)@:
--   https://www.wolframalpha.com/input/?i=plot+(1/(1-x)+-+1/x)
--
-- - @\x -> tan x@:
--   https://www.wolframalpha.com/input/?i=plot+tan(x)
--
-- All of these can be made more uniform by scaling them by a
-- constant, e.g. @\x -> 100000 * tan x@.

{- FIXME: this is only used for fromReal'; see comments for it above
-- | The derivative of the identify function, returning @LogFloat@.
fromRealId' :: Double -> LogFloat
fromRealId' = logFloat
-}

-- | Biject the open interval @(lb,ub)@ onto the reals.
toRealLbUb :: Floating a => a -> a -> a -> a
toRealLbUb lb ub x = r
  where
    -- Biject @(lb,ub)@ onto @(0,1)@
    p = (x - lb) / (ub - lb)
    -- Biject @(0,1)@ onto the reals
    --r = log (p / (1 - p))
    r = (2*p - 1) / (p - p*p)

-- | Biject the reals on the open interval @(lb,ub)@
fromRealLbUb :: Floating a => a -> a -> a -> a
fromRealLbUb lb ub r = x
  where
    -- Inverse of @\p -> log (p / 1 - p)@, except that we have a special case
    -- for infinite values of exp(-r), to prevent us getting NaN values for AD
    -- exp_neg_r = exp (-r)
    -- p = if isInfinite exp_neg_r then 0 else 1 / (1 + exp_neg_r)
    p = (r - 2 + sqrt (r*r + 4)) / (2*r)
    -- Inverse of @\x -> (x - lb) / (ub - lb)@.
    x = p * (ub - lb) + lb

{-
-- | Derivative of 'fromRealLbUb'.
fromRealLbUb' :: R -> R -> R -> LogFloat
fromRealLbUb' lb ub r =
  -- The below is an expansion of
  -- @log ((ub - lb) * (exp (-r) / (1 + exp (-r))**2))@.
  --
  -- Here we use @log1p@ -- an implementation of @\p -> log (1 + p)@
  -- that's optimized for small @p@ -- from
  -- @Data.Numeric.LogFloat@. This implementation of @log1p@ will use
  -- an optimized C implementation if compiled with the @useffi@ flag,
  -- which is supposed to be enabled by default.
  --
  -- The @log-domain@ package that provides an native Haskell
  -- implementation of @log1p@, I think.
  logToLogFloat $ log (ub - lb) - r - 2 * log1p (exp (- r))
-}

-- | Biject the open interval @(0,\infty)@ onto the reals, using the piecewise
-- function that maps @x@ in @(0,1)@ to @log x@ and otherwise maps @x@ to @x-1@.
toRealZeroInftyPW :: Double -> Double
toRealZeroInftyPW x = if x < 1 then log x else x - 1

-- | Biject the reals on the open interval @(0,\infty)@, using the piecewise
-- function that maps negative @x@ to @exp x@ and otherwise maps @x@ to @x+1@.
fromRealZeroInftyPW :: Double -> Double
fromRealZeroInftyPW x = if x < 0 then exp x else x + 1

-- | Biject the open interval @(lb,\infty)@ onto the reals.
toRealLbInfty :: Double -> Double -> R
toRealLbInfty lb x = log (x - lb)

-- | Biject the reals onto the open interval @(lb,\infty)@.
fromRealLbInfty :: Double -> Double -> R
fromRealLbInfty lb r = exp r + lb

-- | Biject the reals onto the open interval @(lb,\infty)@ in log-space
fromRealLbInfty' :: Double -> Double -> Prob
fromRealLbInfty' lb r = logRToProb lb + logRToProb r

-- | Biject the open interval @(-\infty,ub)@ onto the reals.
toRealInftyUb :: Double -> Double -> R
toRealInftyUb ub x = - log (ub - x)

-- | Biject the reals onto the open interval @(-\infty,ub)@.
fromRealInftyUb :: Double -> Double -> R
fromRealInftyUb ub r = - (exp (- r) - ub)

-- | Biject the reals onto the open interval @(lb,\infty)@ in log-space
fromRealInftyUb' :: Double -> Double -> Prob
fromRealInftyUb' _ub _r =
  error "FIXME: fromRealInftyUb' is not right!"
  -- logRToProb ub + logRToProb (- r)

----------------------------------------------------------------------
-- * Example distribution types
----------------------------------------------------------------------

-- | Evaluate the density of a normal distribution at value @r@. This is
-- "unchecked" in that it assumes @sigma@ is non-negative.
normalDensityUnchecked :: Floating r => r -> r -> r -> Log.Log r
normalDensityUnchecked mu sigma x =
  Log.Exp $ - 0.5 * sq ((x - mu) / sigma) - log sigma - halfLogTwoPi
  where
    sq n = n * n
    halfLogTwoPi = 0.5 * log (2 * pi)

-- | Evaluate the density of a normal distribution at value @r@
normalDensityGen :: (Ord r, Floating r, Show r) => r -> r -> r -> Log.Log r
normalDensityGen mu sigma x =
  if sigma <= 0 then
    error $ "normalDensity: sigma is <= 0: sigma = " ++ show sigma
  else
    normalDensityUnchecked mu sigma x

-- | Evaluate the density of a normal distribution at value @r@
normalDensity :: Double -> Double -> Double -> Prob
normalDensity mu sigma x = Prob $ normalDensityGen mu sigma x

data StdNormal = StdNormal deriving Show
type instance Support StdNormal = R
instance PDFDist StdNormal where
  distDensity StdNormal x = logRToProb $ - 0.5 * sq x - halfLogTwoPi
    where
    sq n = n * n
    halfLogTwoPi = 0.5 * log (2 * pi)

instance Continuous StdNormal where
  toReal _ = id
  fromReal _ = id
  --fromReal' _ = fromRealId'

-- | The normal distribution
data Normal = Normal R R deriving Show
type instance Support Normal = R

instance PDFDist Normal where
  distDensity (Normal mu sigma) r = normalDensity mu sigma r

instance Continuous Normal where
  toReal _ = id
  fromReal _ = id
  --fromReal' _ = fromRealId'

----------------------------------------------------------------

-- | Multivariate normal distribution.
--
-- Our multivariate normal of @k@ dimensions is parameterized by the
-- mean vectur @mu = [mu1,...,muk]@ and the *Cholesky factor* @c@ of
-- the covariance matrix @Sigma@. I.e., for multivariate normal with
-- mean @mu@ and covariance matrix @Sigma@, we use
--
-- > MVNormal mu c
--
-- for
--
-- > transpose c * c = Sigma
--
-- The requirements for @c@ to be well formed are that
--
-- - @c@ is upper triangular.
--
-- - all diagonal entries of @c@ are positive.
--
-- There are several reasons to prefer the Cholesky factor @c@ to the
-- covariance matrix @Sigma@:
--
-- - computing the PDF is more efficient using @c@.
--
-- - the sampling algorithm uses @c@, so we need to compute it anyway.
--
-- - all upper triangular matrices with positive diagonal entries are
--   valid Cholesky factors, and a matrix is positive definite iff it
--   has a Cholesky factorization, and the Cholesky factorization is
--   unique. So, it's easy to uniformly sample the space of
--   multivariate normals by uniformly sampling the space upper
--   triangular matrices with positive diagonal entries. We care about
--   sampling multivariate normals e.g. when using multivariate
--   normals as a variational family in Black Box Variation Inference.
--
-- There is a more general definition of multivariate normal which
-- only requires non-negative entries on the diagonal of @c@, where
-- zero values correspond to zero variance random variables,
-- i.e. constants, but we don't support those here (the PDFs would be
-- Dirac deltas).
--
-- A covariance matrix @Sigma@ can be converted into a Cholesky factor
-- @c@ using the @Numeric.LinearAlgebra.chol@ function:
--
-- > c = chol Sigma
--
-- The covariance matrix @Sigma@ must be symmetric and positive
-- definite; you can use @Numeric.LinearAlgebra.trustsym@ to construct
-- it.
data MVNormal = MVNormal (Vector Double) (Matrix Double) deriving Show

type instance Support MVNormal = Vector Double

instance PDFDist MVNormal where
  distDensity (MVNormal mu c) x =
    mvnDensityMuC mu c x

instance (Monad m, SampleableIn m Normal) => SampleableIn m MVNormal where
  -- https://en.wikipedia.org/wiki/Multivariate_normal_distribution#Drawing_values_from_the_distribution
  distSample (MVNormal mu c) = do
    z <- V.fromList <$> (replicateM (size mu) $ distSample (Normal 0 1))
    -- Our Cholesky factorization is @Sigma = transpose c * c@ and
    -- Wikipedia has @Sigma = c * transpose c@, so we need to
    -- transpose here.
    return $ mu + (tr c #> z)

-- | Multivariate normal density in terms of Cholesky factor.
mvnDensityMuC :: Vector Double -> Matrix Double -> Vector Double -> Prob
mvnDensityMuC mu c x =
  if not isValidCholeskyFactor
  then error "distDensity: Cholesky factor is malformed!"
  -- https://en.wikipedia.org/wiki/Multivariate_normal_distribution#Likelihood_function.
  else logRToProb $ -0.5 * (logAbsDet + prod + k * log2pi)
  where
    log2pi = log (2 * pi)
    k = fromIntegral $ size x
    -- We have
    --
    -- > Sigma = transpose c * c
    --
    -- and so
    --
    -- > det Sigma = det c * det c .
    --
    -- We know @det c > 0@ since the diag is positive.
    logAbsDet = 2 * (log $ V.product (takeDiag c))
    -- Here @cholSolve@ solves a linear system for the matrix @Sigma@
    -- for which @c@ is the Cholesky factor. I.e. if
    --
    -- > u == cholSolve m v
    --
    -- then
    --
    -- > transpose c * c * v == u .
    prod = (x - mu) <.> flatten (cholSolve c (asColumn $ x - mu))

    isValidCholeskyFactor = all (> 0) (V.toList $ takeDiag c)

-- | Multivariate normal density in terms of covariance matrix @Sigma@.
--
-- Can use this to test the other implementation above; see
-- 'testMvDensity' below.
mvnDensityMuSigma :: Vector Double -> Matrix Double -> Vector Double -> Prob
mvnDensityMuSigma mu sigma x =
  if signDet < 0
  then error "distDensity: matrix is not positive definite!"
  -- https://en.wikipedia.org/wiki/Multivariate_normal_distribution#Likelihood_function.
  else logRToProb $ -0.5 * (logAbsDet + prod + k * log2pi)
  where
    log2pi = log (2 * pi)
    k = fromIntegral $ size x
    (sigmaInv, (logAbsDet, signDet)) = invlndet sigma
    prod = (x - mu) <.> (sigmaInv #> (x - mu))

-- | Check that the two mv normal density functions agree.
--
-- They agree if this function returns a small number.
testMvnDensity :: Vector Double -> Matrix Double -> Vector Double -> Double
testMvnDensity mu c x =
   abs $ (probToR $ mvnDensityMuSigma mu (tr c <> c) x) -
         (probToR $ mvnDensityMuC mu c x)

-- | Should return a smalllllll number.
testMvnDensityExample :: Double
testMvnDensityExample = sum [ testMvnDensity mu c x | x <- xs ]
  where
    mu = V.fromList [1,2]
    c = chol (trustSym $ (2><2) [1,0.5,0.5,1])
    xs = [ V.fromList [x0,x1] | x0 <- [-5,-4.5..5] , x1 <- [-5,-4.5..5] ]

----------------------------------------------------------------

-- | The uniform distribution
data Uniform = Uniform Double R deriving Show
type instance Support Uniform = R

uniformDensityGen :: (Ord r, RealFloat r, Log.Precise r) =>
                     r -> r -> r -> Log.Log r
uniformDensityGen lb ub r
  | lb >= ub =
    error "Malformed uniform distribution! Lower bound >= upper bound!"
  | r >= lb && r < ub =
    -- The expression 1 / (ub - lb) in log-space
      Log.Exp $ negate $ log $ ub - lb
  | otherwise = 0

uniformDensity :: Double -> Double -> Double -> Prob
uniformDensity lb ub r
  | lb >= ub =
    error "Malformed uniform distribution! Lower bound >= upper bound!"
  | r >= lb && r < ub = 1 / rToProb (ub - lb)
  | otherwise = 0

instance PDFDist Uniform where
  distDensity (Uniform lb ub) = uniformDensity lb ub

instance Continuous Uniform where
  toReal (Uniform lb ub) = toRealLbUb lb ub
  fromReal (Uniform lb ub) = fromRealLbUb lb ub
  --fromReal' (Uniform lb ub) = fromRealLbUb' lb ub

data StudentT = StudentT Double deriving Show
type instance Support StudentT = R

instance Continuous StudentT where
  toReal _ = id
  fromReal _ = id
  --fromReal' _ = fromRealId'

data Cauchy = Cauchy deriving Show
type instance Support Cauchy = R
instance PDFDist Cauchy where
  distDensity Cauchy x = logRToProb $ - log (1 + sq x) - log pi
    where sq n = n * n

instance Continuous Cauchy where
  toReal _ = id
  fromReal _ = id
  --fromReal' _ = fromRealId'

data For d = forall t. For [t] (t -> d)
type instance Support (For d) = [Support d]
instance PDFDist d => PDFDist (For d) where
  distDensity (For xs f) ys =
    product [distDensity (f x) y | (x,y) <- zip xs ys]

data StdUniform = StdUniform deriving Show
type instance Support StdUniform = R

instance PDFDist StdUniform where
  distDensity _ = uniformDensity 0 1

instance Continuous StdUniform where
  toReal _ = toRealLbUb 0 1
  fromReal _ = fromRealLbUb 0 1
  --fromReal' _ = fromRealLbUb' 0 1

-- | The categorical distribution, that picks a natural number between 1 and @n@
-- from a list of probabilisties of each number. Note that the probabilities
-- need not be normalized, e.g., the list @[1,1,1]@ is treated the same as
-- @[1/3,1/3,1/3]@, i.e., that each of 0, 1, and 2 has equal probability.
data Categorical = Categorical [Prob] deriving Show
type instance Support Categorical = Int

instance PDFDist Categorical where
  distDensity (Categorical ws) n =
    let total_w = sum ws in
    if n >= length ws then 0 else ws!!n / total_w


data Exponential = Exponential R deriving Show
type instance Support Exponential = R

exponentialDensityUnchecked :: (RealFloat a, Log.Precise a) =>
                               a -> a -> Log.Log a
exponentialDensityUnchecked rate x = Log.Exp $ log rate - rate * x

exponentialDensity :: (Ord a, RealFloat a, Log.Precise a) => a -> a -> Log.Log a
exponentialDensity rate x =
  if rate > 0 then exponentialDensityUnchecked rate x else 0

instance PDFDist Exponential where
  distDensity (Exponential rate) = Prob . exponentialDensity rate


data Beta = Beta R R deriving Show
type instance Support Beta = R

betaDensityUnchecked :: (HasGamma a, Floating a) => a -> a -> a -> Log.Log a
betaDensityUnchecked alpha beta x =
  Log.Exp $
  ((alpha - 1) * log x) + ((beta - 1) * log (1 - x)) -
  (logGamma alpha + logGamma alpha - logGamma (alpha + beta))

betaDensity :: (Ord a, HasGamma a, RealFloat a, Log.Precise a) =>
               a -> a -> a -> Log.Log a
betaDensity alpha beta x =
  if x > 0 && x < 1 then betaDensityUnchecked alpha beta x else 0

-- | Compute the PDF of the Beta distribution where the argument is already in
-- log space
betaDensityLog :: (Ord a, HasGamma a, RealFloat a, Log.Precise a) =>
                  a -> a -> Log.Log a -> Log.Log a
betaDensityLog alpha beta x =
  if x > 0 && x < 1 then
    Log.Exp $
    ((alpha - 1) * Log.ln x) + ((beta - 1) * Log.ln (1 - x)) -
    (logGamma alpha + logGamma alpha - logGamma (alpha + beta))
  else 0

instance PDFDist Beta where
  distDensity (Beta alpha beta) = Prob . betaDensity alpha beta


data Gamma = Gamma R R deriving Show
type instance Support Gamma = R

-- | Calculate the PDF of the gamma distribution, given shape parameter @k@ and
-- scale parameter @theta@, but without the @1 / (gamma k * theta ** k)@
-- normalization constant
relativeGammaDensity :: Floating a => a -> a -> a -> Log.Log a
relativeGammaDensity k theta x =
  Log.Exp $ (k - 1) * log x - (x / theta)

-- | Calculate the PDF of the gamma distribution, assuming @x > 0@, given shape
-- parameter @k@ and scale parameter @theta@
gammaDensityUnchecked :: (HasGamma a, Floating a) => a -> a -> a -> Log.Log a
gammaDensityUnchecked k theta x =
  Log.Exp (Log.ln (relativeGammaDensity k theta x) - logGamma k - k * log theta)

-- | Calculate the PDF of the gamma distribution, given shape parameter @k@ and
-- scale parameter @theta@
gammaDensity :: (Ord a, HasGamma a, RealFloat a, Log.Precise a) =>
                a -> a -> a -> Log.Log a
gammaDensity k theta x =
  if x <= 0 then 0 else gammaDensityUnchecked k theta x

instance PDFDist Gamma where
  distDensity (Gamma k theta) = Prob . gammaDensity k theta

data Dirichlet = Dirichlet [R] deriving Show
type instance Support Dirichlet = [R]

-- | The log of the multivariate beta function
logMVBeta :: (HasGamma a, Floating a) => [a] -> Log.Log a
logMVBeta alphas =
  -- Gamma (a_1) * ... * Gamma (a_n) / Gamma (a_1 + ... + a_n) in log space
  Log.Exp $ sum (map logGamma alphas) - logGamma (sum alphas)

-- | Calculate the density of the Dirichlet distribution at any type that
-- supports the gamma function
dirichletDensity :: (HasGamma a, Floating a) => [a] -> [a] -> Log.Log a
dirichletDensity alphas xs =
  -- x_1 ** (alpha_1 - 1) * ... * x_n ** (alpha_n - 1) / Beta (alphas)
  Log.Exp $
  sum (zipWith (\alpha x -> (alpha - 1) * log x) alphas xs) -
  Log.ln (logMVBeta alphas)

-- | Calculate the density of the Dirichlet distribution over log space
dirichletDensityLog :: (HasGamma a, Floating a) => [a] -> [Log.Log a] ->
                       Log.Log a
dirichletDensityLog alphas xs =
  -- x_1 ** (alpha_1 - 1) * ... * x_n ** (alpha_n - 1) / Beta (alphas)
  Log.Exp $
  sum (zipWith (\alpha x -> (alpha - 1) * Log.ln x) alphas xs) -
  Log.ln (logMVBeta alphas)

instance PDFDist Dirichlet where
  distDensity (Dirichlet alphas) xs = Prob $ dirichletDensity alphas xs

data Bernoulli = Bernoulli Double deriving Show

data Binomial = Binomial Int Double deriving Show

data Wishart = Wishart (Matrix Double) Double deriving Show
type instance Support Wishart = Matrix Double
instance PDFDist Wishart where
  distDensity (Wishart _scaleChol _df) _x = undefined

-- | A dirac delta distribution, that has a 100 percent chance of returning a
-- given constant value
data Dirac a = Dirac a deriving Show
type instance Support (Dirac a) = a

instance Eq a => PDFDist (Dirac a) where
  -- FIXME: this density is not really correct for R; it should really be
  -- infinite for continuous functions and 1 for discrete ones
  distDensity (Dirac a) x = if a == x then 1 else 0

-- | A technically invalid distribution, that always returns the value @x@ but
-- always has a score of @1@
data DontCare a = DontCare a deriving Show
type instance Support (DontCare a) = a

instance PDFDist (DontCare a) where
  distDensity (DontCare _) _ = 1

----------------------------------------------------------------------
-- * Continuity
----------------------------------------------------------------------

class Continuous (d f) => ReprContinuous d f
instance Continuous (d f) => ReprContinuous d f

-- | This type class states that monad @m@ supports distribution type @d@ by
-- allowing distributions of type @d@ to be randomly sampled in @m@
class Monad m => ReprSampleableIn m d f where
  distSampleRepr :: d f -> m (f (ReprSupport d))

class DiffContinuous d f where
  toRealF   :: d f -> f (ReprSupport d) -> f R
  fromRealF :: d f -> f R -> f (ReprSupport d)

class DiffPDF d f where
  distDensityF :: d f -> f (ReprSupport d) -> f Prob

{-
instance DiffContinuous ReprNormal AD.Forward where
  toRealF _ d = d
  fromRealF _ d = d

instance DiffPDF ReprNormal AD.Forward where
  distDensityF (ReprNormal mu sigma) x =
    if sigma <= 0
      then error $ "distDensityAD Normal: sigma is <= 0: sigma = " ++ show sigma
           -- FIXME: instead of using exp below, figure out how to do an
           -- adToProb that takes a real in log space and preserves
      else adToProb $ exp $ -0.5 * sq((x - mu) / sigma) - log sigma - halfLogTwoPi
      where sq n = n * n
            halfLogTwoPi = 0.5 * log (2 * pi)

instance DiffContinuous ReprUniform AD.Forward where
  toRealF (ReprUniform lb ub) =
    toRealLbUbNum lb ub
  fromRealF (ReprUniform lb ub) =
    fromRealLbUbNum lb ub

instance DiffPDF ReprUniform AD.Forward where
  distDensityF (ReprUniform lb ub) _
    | lb >= ub = error "Malformed uniform distribution! Lower bound >= upper bound!"
    | otherwise =
      (1 / adToProb (lb - ub))
-}

----------------------------------------------------------------------
-- Entropy
----------------------------------------------------------------------

-- | FIXME: document this!
class Entropy d where
  entropy :: d -> Double

instance Entropy Normal where
  entropy (Normal _mu sigma) = k + log sigma
    where
    k = 0.5 * (1 + log (2 * pi))

----------------------------------------------------------------------
-- * The ReprDistribution stuff
----------------------------------------------------------------------

-- | This defines the support type of a distribution
type family ReprSupport (d :: (* -> *) -> *) :: *

data ReprNormal f = ReprNormal (f R) (f R)
type instance ReprSupport ReprNormal = R

data ReprUniform f = ReprUniform (f R) (f R)
type instance ReprSupport ReprUniform = R

data ReprCauchy f = ReprCauchy
type instance ReprSupport ReprCauchy = R

data ReprCategorical f = ReprCategorical [f Prob]
type instance ReprSupport ReprCategorical = Int

-- FIXME: this uses different vector and matrix types than MVNormal
data ReprMVNormal f = ReprMVNormal (f RMatrix) (f RMatrix)
type instance ReprSupport ReprMVNormal = RMatrix
