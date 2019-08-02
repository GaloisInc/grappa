{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ForeignFunctionInterface #-}

module Language.Grappa.Interp.PVIE where

import Data.Functor.Compose
-- import Data.Functor.Product
import Control.Lens
import Control.Monad.State
import Control.Monad.Primitive
import qualified Numeric.Log as Log

import Foreign.Ptr
import Foreign.ForeignPtr

import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Storable.Mutable as SMV

import qualified Numeric.AD.Mode.Reverse as ADR
import qualified Numeric.AD.Internal.Reverse as ADR
import qualified Data.Reflection as ADR (Reifies)

import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals

import Language.Grappa.Rand.MWCRandM
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC


----------------------------------------------------------------------
-- * Dimensionality Expressions
----------------------------------------------------------------------

-- | A "dimensionality variable"
-- (FIXME: explain what this means: an index into a 'VIDimAsgn'?)
newtype VIDimVar = VIDimVar { viDimVarIx :: Int } deriving Eq

-- | Build a list of the first @n@ dimensionality variables
viDimVars :: Int -> [VIDimVar]
viDimVars n = take n $ map VIDimVar $ [0 ..]

-- | The "first" dimensionality variable
zeroVar :: VIDimVar
zeroVar = VIDimVar 0

-- | Get the next dimensionality variable after the given one
nextVar :: VIDimVar -> VIDimVar
nextVar (VIDimVar i) = (VIDimVar (i+1))

maxVar :: VIDimVar -> VIDimVar -> VIDimVar
maxVar (VIDimVar v1) (VIDimVar v2) = VIDimVar $ max v1 v2

-- | An assignment to dimensionality variables, which should be non-negative
newtype VIDimAsgn = VIDimAsgn [Int]

-- | Create an assignment where all variables below the given one are set to 0
zeroAsgn :: VIDimVar -> VIDimAsgn
zeroAsgn (VIDimVar i) = VIDimAsgn $ take i $ repeat 1

-- | Increment the assignment to a particular dimensionality variable
incrAsgn :: VIDimVar -> VIDimAsgn -> VIDimAsgn
incrAsgn (VIDimVar i) (VIDimAsgn asgn) = VIDimAsgn (over (ix i) (+ 1) asgn)

-- | Increment the assignment to a particular dimensionality variable
incrAsgnAll :: VIDimAsgn -> VIDimAsgn
incrAsgnAll (VIDimAsgn asgn) = VIDimAsgn (map (+1) asgn)

-- | Look up the value of a dimensionality variable in an assignment
viDimVarVal :: VIDimVar -> VIDimAsgn -> Int
viDimVarVal (VIDimVar i) (VIDimAsgn ns) = ns !! i

-- | An expression for the dimensionality of variational inference parameters in
-- terms of some dimensionality variables, given as a function on the values of
-- those variables along with an indicator of how many variables are
-- needed. Note that this function should always return a non-negative value.
data VIDim = VIDim {
  evalVIDim :: VIDimAsgn -> Int,
  viDimFirstUnusedVar :: VIDimVar
  }

-- | Build a constant dimensionality
constVIDim :: Int -> VIDim
constVIDim k = VIDim (const k) zeroVar

-- | Build a variable dimensionality
varVIDim :: VIDimVar -> VIDim
varVIDim v = VIDim (viDimVarVal v) (nextVar v)

-- | Apply a binary operation to a 'VIDim', ensuring the resulting dimension
-- evaluation is non-negative
viDimBinOp :: (Int -> Int -> Int) -> VIDim -> VIDim -> VIDim
viDimBinOp binop (VIDim eval1 v1) (VIDim eval2 v2) =
  VIDim (\asgn -> max (eval1 asgn `binop` eval2 asgn) 0) (maxVar v1 v2)

instance Num VIDim where
  (+) = viDimBinOp (+)
  (-) = viDimBinOp (-)
  (*) = viDimBinOp (*)
  abs dim = dim -- dimensions are always non-negative
  signum _ = 1 -- satisfies abs dim * signum dim = dim (up to equivalence)
  fromInteger = constVIDim . fromInteger


----------------------------------------------------------------------
-- * Differentiable Functions
----------------------------------------------------------------------

type Params = SV.Vector Double
type MutParams = SMV.MVector (PrimState IO) Double
type ParamsGrad = SMV.MVector (PrimState IO) Double

-- | Create a normal 'Vector' for a (small number of) 'Params'. This is needed
-- in order to use the reverse-mode AD 'ADR.grad' function.
vectorOfParams :: Int -> Params -> Vector Double
vectorOfParams n params = V.generate n (params SV.!)

-- | Helper class to write "differentiable" functions on our parameters
class FromDouble a where
  fromDouble :: Double -> a

instance FromDouble Double where
  fromDouble = id

instance ADR.Reifies s ADR.Tape => FromDouble (ADR.Reverse s Double) where
  fromDouble = ADR.auto

-- | All the typeclasses we want for types used in differentiable functions
type DiffConstr a = (RealFloat a, Ord a, Show a, FromDouble a)

-- | The type of functions that are differentiable using AD
type DiffFun = forall r. DiffConstr r => Vector r -> r

-- | Take a differentiable function on @n@ (the first argument) variables and
-- turn it into a function that computes its gradient, scaled by the given
-- factor, and accumulates the result into the supplied mutable vector
scaledGrad :: Int -> Double -> DiffFun -> Params -> ParamsGrad -> IO ()
scaledGrad n scale f params params_grad =
  let raw_grad = ADR.grad f (vectorOfParams n params) in
  forM_ [0 .. n-1] $ \i ->
  SMV.modify params_grad ((scale * raw_grad V.! i) +) i

-- | Take a differentiable function on @n@ (the first argument) variables and
-- turn it into a function that computes its gradient, accumulating the result
-- into the supplied mutable vector, and also returns the result of the function
gradAndRet :: Int -> DiffFun -> Params -> ParamsGrad -> IO Double
gradAndRet n f params params_grad =
  do scaledGrad n 1 f params params_grad
     return (f $ vectorOfParams n params)


----------------------------------------------------------------------
-- * Distribution Approximators for Variational Inference
----------------------------------------------------------------------

type EntropyFun = VIDimAsgn -> Params -> ParamsGrad -> IO Double
type GradPDFFun a = Double -> a -> VIDimAsgn -> Params -> ParamsGrad -> IO ()
type GrowFun = VIDimAsgn -> VIDimAsgn -> Params -> MutParams -> IO ()

-- | The trivial entropy function for the only distribution over ()
unitEntropyFun :: EntropyFun
unitEntropyFun _ _ _ = return 0

-- | Add two independent entropy functions, where the first has the given
-- dimensionality expression
addEntropyFuns :: VIDim -> EntropyFun -> EntropyFun -> EntropyFun
addEntropyFuns dim1 f1 f2 =
  \asgn ps ps_grad ->
  (+) <$>
  f1 asgn (SV.take (evalVIDim dim1 asgn) ps)
  (SMV.take (evalVIDim dim1 asgn) ps_grad)
  <*>
  f2 asgn (SV.drop (evalVIDim dim1 asgn) ps)
  (SMV.drop (evalVIDim dim1 asgn) ps_grad)

-- | The trivial log PDF function with 0 gradient
unitGradPDFFun :: GradPDFFun a
unitGradPDFFun _ _ _ _ _ = return ()

-- | Add two log PDF functions, assuming they are independent, given a
-- volume-preserving map from the codomain type to the two domain types
-- (represented as a pair of functions instead of a function to a pair) along
-- with a dimensionality expression for the number of params of the first
addGradPDFFuns :: (a -> b) -> (a -> c) -> VIDim ->
                  GradPDFFun b -> GradPDFFun c -> GradPDFFun a
addGradPDFFuns split_l split_r dim1 f1 f2 =
  \scale a asgn ps ps_grad ->
  f1 scale (split_l a) asgn (SV.take (evalVIDim dim1 asgn) ps)
  (SMV.take (evalVIDim dim1 asgn) ps_grad)
  >>
  f2 scale (split_r a) asgn (SV.drop (evalVIDim dim1 asgn) ps)
  (SMV.drop (evalVIDim dim1 asgn) ps_grad)

-- | The trivial 'viDistGrowParams' function for no parameters
unitGrowFun :: GrowFun
unitGrowFun _ _ _ _ = return ()

-- | Combine two 'viDistGrowParams' fields, given the dimensionality expression
-- for the first one
combineGrowFuns :: VIDim -> GrowFun -> GrowFun -> GrowFun
combineGrowFuns dim1 f1 f2 =
  \old_asgn new_asgn params mut_params ->
  f1 old_asgn new_asgn (SV.take (evalVIDim dim1 old_asgn) params)
  (SMV.take (evalVIDim dim1 new_asgn) mut_params)
  >>
  f2 old_asgn new_asgn (SV.drop (evalVIDim dim1 old_asgn) params)
  (SMV.drop (evalVIDim dim1 new_asgn) mut_params)


-- | A family of distributions for variational inference
data VIDistFam a =
  VIDistFam
  {
    -- | The dimensionality of the parameters
    viDistDim :: VIDim,

    -- | Sampling function to randomly generate an @a@ given 'viDistDim'
    -- 'Double'-valued parameters
    viDistSample :: VIDimAsgn -> Params -> MWCRandM a,

    -- | Evaluate the entropy at the given parameters and also add the gradient
    -- of the entropy with respect to those parameters into the mutable vector
    viDistEntropy :: EntropyFun,

    -- | Evaluate the gradient with respect to the parameters of the log PDF of
    -- the distribution, scaled by the supplied factor, and add the result to
    -- the supplied mutable vector
    viDistScaledGradPDF :: GradPDFFun a,

    -- | Grow a vector of parameters from the dimensionality implied by one
    -- assignment to that of another, larger one, storing the result in the
    -- given mutable vector (assuming it has the correct size)
    viDistGrowParams :: GrowFun
  }

-- | An "expression" for building up a family of distributions, which keeps
-- track of how many dimensionality variables we have used so far
newtype VIDistFamExpr a =
  VIDistFamExpr { runVIDistFamExpr :: State VIDimVar (VIDistFam a) }

-- | Evaluate a distribution family expression into a distribution family
evalVIDistFamExpr :: VIDistFamExpr a -> VIDistFam a
evalVIDistFamExpr (VIDistFamExpr m) = evalState m (VIDimVar 0)

-- | The constant distribution (also known as the delta distribution), that
-- returns a single value with unit probability
deltaVIFamExpr :: Eq a => a -> VIDistFamExpr a
deltaVIFamExpr a =
  simpleVIFamExpr 0 (\_ -> return a) (\_ -> 0)
  (\x _ -> if x == a then 0 else log 0)

-- | Transform a distribution family over one type to another type using a
-- volume-preserving isomorphism. A volume-preserving map is one that does not
-- squeeze any objects closer together or move them farther apart; the technical
-- definition is that it preserves the measures of all sets with respect to the
-- reference measure on the two spaces.
xformVIDistFam :: (a -> b) -> (b -> a) -> VIDistFam a -> VIDistFam b
xformVIDistFam f_to f_from (VIDistFam {..}) =
  VIDistFam
  {
    viDistSample = (\asgn ps -> fmap f_to $ viDistSample asgn ps),
    viDistScaledGradPDF = (\scale a -> viDistScaledGradPDF scale (f_from a)),
    ..
  }

-- | Transform a distribution family expression over one type to another type
-- using a volume-preserving isomorphism; see 'xformVIDistFam'.
xformVIDistFamExpr :: (a -> b) -> (b -> a) -> VIDistFamExpr a -> VIDistFamExpr b
xformVIDistFamExpr f_to f_from expr =
  VIDistFamExpr (xformVIDistFam f_to f_from <$> runVIDistFamExpr expr)

-- | Build a distribution family expression for a "simple" distribution, meaning
-- it is not a composite of multiple distributions on sub-components.  Such a
-- distribution is defined by a dimensionality expression, a sampling function,
-- and differentiable functions for the entropy and log PDF.
simpleVIFamExpr :: VIDim ->
                   (Params -> MWCRandM a) ->
                   DiffFun ->
                   (a -> DiffFun) ->
                   VIDistFamExpr a
simpleVIFamExpr dim sampleFun entropyFun pdfFun =
  VIDistFamExpr $ return $ VIDistFam
  { viDistDim = dim
  , viDistSample =
      (\asgn ps -> sampleFun (SV.take (evalVIDim dim asgn) ps))
  , viDistEntropy =
      (\asgn -> gradAndRet (evalVIDim dim asgn) entropyFun)
  , viDistScaledGradPDF =
      (\scale a asgn -> scaledGrad (evalVIDim dim asgn) scale (pdfFun a))
  , viDistGrowParams =
      (\old_asgn _ params mut_params ->
        forM_ [0 .. evalVIDim dim old_asgn - 1] $ \i ->
        SMV.write mut_params i (params SV.! i))
  }

-- | Build a distribution family expression for the normal distribution, where
-- we use absolute value of @sigma@ to map it to the non-negative reals
normalVIFamExpr :: VIDistFamExpr R
normalVIFamExpr =
  simpleVIFamExpr 2 (\ps -> mwcNormal (ps SV.! 0) (ps SV.! 1))
  (\ps -> 0.5 * (1 + log (2 * pi)) + log (ps V.! 1))
  (\x ps -> Log.ln $ normalDensityUnchecked (ps V.! 0) (abs (ps V.! 1)) (fromDouble x))

-- | Build a distribution family expression for the uniform distribution over
-- the range @(min a b, max a b]@
uniformVIFamExpr :: VIDistFamExpr R
uniformVIFamExpr =
  simpleVIFamExpr 2 (\ps -> mwcUniform (ps SV.! 0) (ps SV.! 1))
  (\ps -> log $ abs (ps V.! 1 - ps V.! 0))
  (\x ps ->
    if min (ps V.! 0) (ps V.! 1) < fromDouble x
       && fromDouble x <= max (ps V.! 0) (ps V.! 1) then
      log $ abs (ps V.! 1 - ps V.! 0)
    else log 0)


-- | Build a distribution family expression for the categorical distribution
-- over @[0,..,n-1]@ with relative probabilities @[a1,..,an]@, with the special
-- case that @n=0@ is treated like @n=1@, meaning it always returns @0@
categoricalVIFamExpr :: VIDim -> VIDistFamExpr Int
categoricalVIFamExpr dim =
  simpleVIFamExpr dim
  (\ps -> random $ MWC.categorical ps)
  (\ps ->
    let p_sum = V.sum ps in
    V.sum $ V.map (\p -> (p / p_sum) * log (p / p_sum)) ps)
  (\x ps ->
    let n = V.length ps in
    if n == 0 && x == 0 then 1 else
      if x < 0 || x >= n then 0 else
        log (ps V.! x))

-- | Bind a fresh dimensionality variable in a distribution family expression
bindDimVIFamExpr :: (VIDim -> VIDistFamExpr a) -> VIDistFamExpr a
bindDimVIFamExpr f =
  VIDistFamExpr $ do
  v <- get
  put $ nextVar v
  runVIDistFamExpr $ f (varVIDim v)

-- | The trivial distribution family expression over the unit type
unitVIDistExpr :: VIDistFamExpr ()
unitVIDistExpr = simpleVIFamExpr 0 (\_ -> return ()) (\_ -> 0) (\_ _ -> 0)

-- | Combine two distribution families into a distribution family over a pair
pairVIDists :: VIDistFam a -> VIDistFam b -> VIDistFam (a,b)
pairVIDists d1 d2 =
  let dim1 = viDistDim d1 in
  VIDistFam
  { viDistDim = dim1 + viDistDim d2
  , viDistSample =
      (\asgn params ->
        (,) <$> viDistSample d1 asgn params <*> viDistSample d2 asgn params)
  , viDistEntropy =
      addEntropyFuns dim1 (viDistEntropy d1) (viDistEntropy d2)
  , viDistScaledGradPDF =
      addGradPDFFuns fst snd dim1 (viDistScaledGradPDF d1) (viDistScaledGradPDF d2)
  , viDistGrowParams =
      combineGrowFuns dim1 (viDistGrowParams d1) (viDistGrowParams d2)
  }


-- | Combine two distribution family expressions using 'pairVIDists'
pairVIDistExprs :: VIDistFamExpr a -> VIDistFamExpr b -> VIDistFamExpr (a,b)
pairVIDistExprs d1 d2 =
  VIDistFamExpr (pairVIDists <$> runVIDistFamExpr d1 <*> runVIDistFamExpr d2)

hlistVIFamExpr :: HList (Compose VIDistFamExpr f) ts ->
                  VIDistFamExpr (HList f ts)
hlistVIFamExpr HListNil =
  xformVIDistFamExpr (const HListNil) (const ()) unitVIDistExpr
hlistVIFamExpr (HListCons d ds) =
  xformVIDistFamExpr (\(a,as) -> HListCons a as) (\(HListCons a as) -> (a,as)) $
  pairVIDistExprs (getCompose d) (hlistVIFamExpr ds)

-- | Build a distribution family expression for a tuple from a tuple of
-- distribution family expressions
tupleVIFamExpr :: TupleF ts (Compose VIDistFamExpr f) (ADT (TupleF ts)) ->
                  VIDistFamExpr (TupleF ts f (ADT (TupleF ts)))
tupleVIFamExpr d_exprs =
  xformVIDistFamExpr hListToTuple tupleToHList $
  hlistVIFamExpr $ tupleToHList d_exprs

-- | The distribution family over lists with a given length whose elements are
-- drawn IID from the supplied distribution family
iidVIFam :: VIDim -> VIDistFam a -> VIDistFam (Vector a)
iidVIFam len d =
  VIDistFam
  { viDistDim = len * viDistDim d
  , viDistSample =
    (\asgn params ->
      V.replicateM (evalVIDim len asgn) (viDistSample d asgn params))
  , viDistEntropy =
    let entr = viDistEntropy d in
    (\asgn ->
      (iterate (addEntropyFuns (viDistDim d) entr) unitEntropyFun
       !! evalVIDim len asgn)
      asgn)
  , viDistScaledGradPDF =
    let pdf = viDistScaledGradPDF d in
    (\scale a asgn ->
      (iterate (addGradPDFFuns V.head V.tail (viDistDim d) pdf) unitGradPDFFun
       !! evalVIDim len asgn)
      scale a asgn)
  , viDistGrowParams =
    let grow = viDistGrowParams d in
    (\asgn ->
      (iterate (combineGrowFuns (viDistDim d) grow) unitGrowFun
       !! evalVIDim len asgn)
      asgn)
  }

-- | The distribution family expression over lists with a given length whose
-- elements are drawn IID from the supplied distribution family expression
iidVIFamExpr :: VIDim -> VIDistFamExpr a -> VIDistFamExpr (Vector a)
iidVIFamExpr len d_expr =
  VIDistFamExpr (iidVIFam len <$> runVIDistFamExpr d_expr)


----------------------------------------------------------------------
-- * Variational Inference, Yay!
----------------------------------------------------------------------

-- | The type of FFI-compatible functions that we can optimize
type FFIOptFun = Int -> Ptr Double -> Ptr Double -> IO Double

foreign import ccall "optimize_lbfgs" optimize_lbfgs
  :: Int -> FunPtr FFIOptFun -> Ptr Double -> IO Double

foreign import ccall "wrapper" wrapFFIOptFun
  :: FFIOptFun -> IO (FunPtr FFIOptFun)

createFFIOptFun :: (Params -> MutParams -> IO Double) ->
                   IO (FunPtr FFIOptFun)
createFFIOptFun f =
  wrapFFIOptFun $ \len params_ptr grad_ptr ->
  do params_frgnptr <- newForeignPtr_ params_ptr
     let params = SV.unsafeFromForeignPtr0 params_frgnptr len
     grad_frgnptr <- newForeignPtr_ grad_ptr
     let grad = SMV.unsafeFromForeignPtr0 grad_frgnptr len
     f params grad

optimize :: (Params -> MutParams -> IO Double) -> MutParams -> IO Double
optimize f mut_params =
  do f_ptr <- createFFIOptFun f
     val <- SMV.unsafeWith mut_params
       (\params_ptr -> optimize_lbfgs (SMV.length mut_params) f_ptr params_ptr)
     freeHaskellFunPtr f_ptr
     return val

-- FIXME HERE: make VIDistFams know how to initialize their params

-- | The amount that PVIE has to improve in an interation to seem "better"
pvie_epsilon :: Double
pvie_epsilon = 1.0e-6

-- | FIXME: make this be a command-line option somehow!
num_samples :: Int
num_samples = 100

-- FIXME HERE: call this something more meaningful!
elbo_with_grad :: MWC.GenIO -> VIDistFam a -> (a -> Double) -> VIDimAsgn ->
                    (Params -> MutParams -> IO Double)
elbo_with_grad g d log_p asgn params grad =
  do samples <-
       replicateM num_samples (runRand g $ viDistSample d asgn params)
     let n = fromIntegral num_samples
     entr <- viDistEntropy d asgn params grad
     forM_ samples $ \samp ->
       viDistScaledGradPDF d (log_p samp / n) samp asgn params grad
     return (entr - (1/n) * sum (map log_p samples))

pvie :: VIDistFam a -> (a -> Double) -> IO (VIDimAsgn, Params, Double)
pvie d log_p = init_pvie where

  -- Initialize PVIE and start it running
  init_pvie :: IO (VIDimAsgn, Params, Double)
  init_pvie = do
    g <- MWC.createSystemRandom
    -- Start with 0 for all dimensionality variables
    let asgn = zeroAsgn $ viDimFirstUnusedVar $ viDistDim d
    -- Allocate and initialize our mutable params
    mut_params <- SMV.new (evalVIDim (viDistDim d) asgn)
    -- FIXME HERE: have VIDistFams initialize their mut_params
    SMV.set mut_params 0
    -- Generate the initial value to try to beat
    val <- optimize (elbo_with_grad g d log_p asgn) mut_params
    params <- SV.unsafeFreeze mut_params
    -- If there are no dimensionality variables in our distribution family, then
    -- there is nothing to increment, so we are done
    if viDimFirstUnusedVar (viDistDim d) == zeroVar then
      outer g asgn params val False
      else
      -- Perform the first iteration of optimizing the dimensionality variables
      outer g asgn params val True

  -- The main outer loop
  outer :: MWC.GenIO -> VIDimAsgn -> Params -> Double -> Bool ->
           IO (VIDimAsgn, Params, Double)
  outer _ asgn params last_val False =
    -- If our last iteration of the outer loop did not improve, we are done, and
    -- return the current assignment, parameters, and value
    return (asgn, params, last_val)

  outer g asgn params last_val True =
    do
      -- Otherwise, start by allocating two new arrays, one for the current
      -- parameters and one for the scratch space. The size should be big enough
      -- for if we increment all dimensionality variables by one, which is the
      -- most we will do in the upcoming iteration of the outer loop.
      new_mut_params <- SMV.new (evalVIDim (viDistDim d) $ incrAsgnAll asgn)
      scratch <- SMV.new (evalVIDim (viDistDim d) $ incrAsgnAll asgn)
      -- Copy the old parameters into the new mutable params
      let new_mut_params_slice = SMV.slice 0 (SV.length params) new_mut_params
      SV.copy new_mut_params_slice params
      new_params <- SV.unsafeFreeze new_mut_params
      -- Start the inner loop at the first dimensionality variable, telling it
      -- that we have not yet improved
      inner g asgn new_params last_val zeroVar scratch False

  -- The main inner loop: takes in the current assignment to dimensionality
  -- variables, the current "best" params for the associated size, the value for
  -- those params, the next dimensionality variable to try to increment,
  -- pre-allocated scratch space for parameters, and whether we have already
  -- seen improvement in this iteration of the outer loop
  inner :: MWC.GenIO -> VIDimAsgn -> Params -> Double -> VIDimVar ->
           MutParams -> Bool -> IO (VIDimAsgn, Params, Double)
  inner g asgn last_params last_val next_var _ improved
    | next_var == viDimFirstUnusedVar (viDistDim d)
    = outer g asgn last_params last_val improved

  inner g asgn last_params last_val next_var scratch improved = do
    -- The next assignment we will try = increment next_var
    let new_asgn = incrAsgn next_var asgn
    -- Copy our current best parameters into our scratch area
    viDistGrowParams d asgn new_asgn last_params scratch
    -- Optimize those parameters
    new_val <- optimize (elbo_with_grad g d log_p asgn) scratch
    -- Test how much we improved
    if last_val - new_val >= pvie_epsilon then
      -- If we did improve, swap last_params and scratch, then iterate
      do new_params <- SV.unsafeFreeze scratch
         new_scratch <- SV.unsafeThaw last_params
         inner g new_asgn new_params new_val (nextVar next_var) new_scratch True
      else
      -- Otherwise, keep the same assignment, params, and scratch
      inner g asgn last_params last_val (nextVar next_var) scratch improved
