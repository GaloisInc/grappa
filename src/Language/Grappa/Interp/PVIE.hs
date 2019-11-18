{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Grappa.Interp.PVIE where

import Data.List
import GHC.Generics hiding (R)
import Data.Functor.Const
import Data.Functor.Compose
-- import Data.Functor.Product
import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Primitive
import Data.IORef
import qualified Numeric.Log as Log

import qualified Data.ByteString.Lazy as BS
import Data.Aeson
import System.IO
import System.IO.Unsafe
import System.Directory (doesFileExist)

import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Numeric.LinearAlgebra.Data as SV (Vector)
import qualified Data.Vector.Generic as SV hiding (Vector)
import qualified Data.Vector.Generic as SVGen
import qualified Data.Vector.Storable.Mutable as SMV

import qualified Numeric.AD.Mode.Reverse as ADR
import qualified Numeric.AD.Internal.Reverse as ADR
import qualified Data.Reflection as ADR (Reifies)

import Numeric.GSL.Minimization

import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals

import Language.Grappa.Rand.MWCRandM
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.PrettyPrint.ANSI.Leijen ((<+>), (<>))

import Options.Applicative

import Debug.Trace


-- | Read JSON file @filename@ and parse it to an @a@, where @filename@ can be
-- @"-"@ to denote 'stdin'
readJSONfile :: FromJSON a => String -> IO a
readJSONfile f =
  withFileContents f $ \contents ->
  case eitherDecode' contents of
    Left err -> error ("Could not parse JSON file " ++ f ++ ": " ++ err)
    Right a -> return a
  where
    withFileContents :: String -> (BS.ByteString -> IO a) -> IO a
    withFileContents "-" k = BS.hGetContents stdin >>= k
    withFileContents filename k =
      withFile filename ReadMode $ \h -> BS.hGetContents h >>= k

-- | Write JSON file @filename@, which can be @"-"@ to indicate 'stdout'
writeJSONfile :: ToJSON a => String -> a -> IO ()
writeJSONfile "-" a = BS.putStr $ encode a
writeJSONfile filename a = encodeFile filename a


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
newtype VIDimAsgn = VIDimAsgn [Int] deriving Generic

instance FromJSON VIDimAsgn where

instance ToJSON VIDimAsgn where
  toEncoding = genericToEncoding defaultOptions

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
type DiffConstr a = (RealFloat a, Ord a, Show a, FromDouble a,
                     HasGamma a, Log.Precise a)

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
-- * Computations Over Parameters
----------------------------------------------------------------------

newtype ParamsT m a = ParamsT (ReaderT (IORef Params) m a)
                    deriving (Functor, Applicative, Monad, MonadTrans)

runParamsT :: MonadIO m => ParamsT m a -> Params -> m a
runParamsT (ParamsT m) params =
  liftIO (newIORef params) >>= runReaderT m

instance MonadIO m => MonadIO (ParamsT m) where
  liftIO m = ParamsT $ liftIO m

class Monad m => MonadParams m where
  getParams :: Int -> m Params

instance MonadParams m => MonadParams (ReaderT r m) where
  getParams n = lift $ getParams n

instance MonadIO m => MonadParams (ParamsT m) where
  getParams n =
    ParamsT $ do r <- ask
                 ps <- liftIO $ readIORef r
                 liftIO $ writeIORef r (SV.drop n ps)
                 return $ SV.take n ps


newtype MutParamsT m a = MutParamsT (ReaderT (IORef MutParams) m a)
                       deriving (Functor, Applicative, Monad, MonadTrans)

runMutParamsT :: MonadIO m => MutParamsT m a -> MutParams -> m a
runMutParamsT (MutParamsT m) mut_params =
  liftIO (newIORef mut_params) >>= runReaderT m


instance MonadIO m => MonadIO (MutParamsT m) where
  liftIO m = MutParamsT $ liftIO m

instance MonadParams m => MonadParams (MutParamsT m) where
  getParams n = MutParamsT $ getParams n

class Monad m => MonadMutParams m where
  getMutParams :: Int -> m MutParams

instance MonadIO m => MonadMutParams (MutParamsT m) where
  getMutParams n =
    MutParamsT $ do r <- ask
                    ps <- liftIO $ readIORef r
                    liftIO $ writeIORef r (SMV.drop n ps)
                    return (SMV.take n ps)

instance MonadMutParams m => MonadMutParams (ReaderT r m) where
  getMutParams n = lift $ getMutParams n


-- | A computation for generating samples of distribution families
type SamplingM = ReaderT VIDimAsgn (ParamsT MWCRandM)

-- | Run a 'SamplingM' computation
runSamplingM :: SamplingM a -> MWC.GenIO -> VIDimAsgn -> Params -> IO a
runSamplingM m gen asgn params =
  runRand gen (runParamsT (runReaderT m asgn) params)

embedSamplingFun :: VIDim -> (Params -> MWCRandM a) -> SamplingM a
embedSamplingFun dim f =
  do asgn <- ask
     params <- getParams (evalVIDim dim asgn)
     lift $ lift $ f params


-- | A computation that consumes a vector of parameters and a vector of mutable
-- parameters, the latter being used for accumulating gradients
type ParamsGradM = ReaderT VIDimAsgn (MutParamsT (ParamsT IO))

runParamsGradM :: ParamsGradM a -> VIDimAsgn -> Params -> MutParams -> IO a
runParamsGradM m asgn params mut_params =
  runParamsT (runMutParamsT (runReaderT m asgn) mut_params) params

-- | Take the scaled gradient of a differentiable function with @n@ parameters
-- and accumulate it into the gradient of the current computation
embedScaledGrad :: VIDim -> DiffFun -> Double -> ParamsGradM ()
embedScaledGrad dim f scale =
  do n <- evalVIDim dim <$> ask
     params <- getParams n
     params_grad <- getMutParams n
     liftIO $ scaledGrad n scale f params params_grad

-- | Evaluate a differentiable function with @n@ parameters and its gradient,
-- returning the value and accumulating the gradient into the gradient of the
-- current computation
embedGradAndRet :: VIDim -> DiffFun -> ParamsGradM Double
embedGradAndRet dim f =
  do n <- evalVIDim dim <$> ask
     params <- getParams n
     params_grad <- getMutParams n
     liftIO $ gradAndRet n f params params_grad

-- | A computation for initializing parameters
type InitM = ReaderT VIDimAsgn (MutParamsT MWCRandM)

runInitM :: InitM a -> MWC.GenIO -> VIDimAsgn -> MutParams -> IO a
runInitM m gen asgn mut_params =
  runRand gen $ runMutParamsT (runReaderT m asgn) mut_params

simpleInitFun :: (VIDimAsgn -> MWCRandM [Double]) -> InitM ()
simpleInitFun initFun =
  do asgn <- ask
     params <- lift $ lift $ initFun asgn
     let params_v = SV.fromList params
     mut_params <- getMutParams (length params)
     liftIO $ SV.copy mut_params params_v

-- | A computation for growing sequences of parameters
type GrowM = ReaderT (VIDimAsgn, VIDimAsgn) (MutParamsT (ParamsT MWCRandM))

runGrowM :: GrowM a -> MWC.GenIO -> VIDimAsgn -> VIDimAsgn ->
            Params -> MutParams -> IO a
runGrowM m gen asgn new_asgn params new_params =
  runRand gen $
  runParamsT (runMutParamsT (runReaderT m (asgn, new_asgn)) new_params) params

simpleGrowFun :: VIDim -> (VIDimAsgn -> MWCRandM [Double]) -> GrowM ()
simpleGrowFun dim initFun =
  do (old_asgn, new_asgn) <- ask
     params <- getParams (evalVIDim dim old_asgn)
     old_mut_params <- getMutParams (evalVIDim dim old_asgn)
     liftIO $ SV.copy old_mut_params params
     new_mut_params <-
       getMutParams (evalVIDim dim new_asgn - evalVIDim dim old_asgn)
     inits_l <- lift $ lift $ lift $ initFun new_asgn
     let inits_v = SV.fromList $ drop (SV.length params) inits_l
     liftIO $ SV.copy new_mut_params inits_v

type PPFun = ReaderT VIDimAsgn (ParamsT IO) PP.Doc

simplePPFun :: VIDim -> String -> PPFun
simplePPFun dim nm =
  do n <- evalVIDim dim <$> ask
     params <- getParams n
     return (PP.text nm <+> PP.tupled (map PP.pretty $ SV.toList params))

applyPPFun :: PPFun -> VIDimAsgn -> Params -> IO PP.Doc
applyPPFun f asgn params = runParamsT (runReaderT f asgn) params


----------------------------------------------------------------------
-- * Distribution Approximators for Variational Inference
----------------------------------------------------------------------

type EntropyFun = ParamsGradM Double
type ScaledGradPDFFun a = Double -> a -> ParamsGradM ()
type InitFun = InitM ()
type GrowFun = GrowM ()

{-
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
-}


-- | A family of distributions for variational inference
data VIDistFam a =
  VIDistFam
  {
    -- | The dimensionality of the parameters
    viDistDim :: VIDim,

    -- | Sampling function to randomly generate an @a@ given 'viDistDim'
    -- 'Double'-valued parameters
    viDistSample :: SamplingM a,

    -- | Evaluate the entropy at the given parameters and also add the gradient
    -- of the entropy with respect to those parameters into the mutable vector
    viDistEntropy :: EntropyFun,

    -- | Evaluate the gradient with respect to the parameters of the log PDF of
    -- the distribution, scaled by the supplied factor, and add the result to
    -- the supplied mutable vector
    viDistScaledGradPDF :: ScaledGradPDFFun a,

    -- | Randomly initialize the parameters of this distribution family
    viDistInit :: InitFun,

    -- | Grow a vector of parameters from the dimensionality implied by one
    -- assignment to that of another, larger one, storing the result in the
    -- given mutable vector (assuming it has the correct size) and initializing
    -- any new parameters
    viDistGrowParams :: GrowFun,

    -- | Pretty-print a distribution given its parameters
    viDistPP :: PPFun
  }


-- | Build a distribution family for a "simple" distribution, meaning it is not
-- a composite of multiple distributions on sub-components.  Such a distribution
-- is defined by a dimensionality expression, a sampling function,
-- differentiable functions for the entropy and log PDF, and an initialization
-- function for the parameters.
simpleVIFam :: String -> VIDim -> (Params -> MWCRandM a) -> DiffFun ->
               (a -> DiffFun) -> (VIDimAsgn -> MWCRandM [Double]) ->
               VIDistFam a
simpleVIFam nm dim sampleFun entropyFun pdfFun initFun =
  VIDistFam
  { viDistDim = dim
  , viDistSample = embedSamplingFun dim sampleFun
  , viDistEntropy = embedGradAndRet dim entropyFun
  , viDistScaledGradPDF =
      (\scale a -> embedScaledGrad dim (pdfFun a) scale)
  , viDistInit = simpleInitFun initFun
  , viDistGrowParams = simpleGrowFun dim initFun
  , viDistPP = simplePPFun dim nm
  }


-- | Build a distribution family for tuples from a tuple of families
tupleVIFam :: TupleF ts (Compose VIDistFam f) (ADT (TupleF ts)) ->
              VIDistFam (TupleF ts f (ADT (TupleF ts)))
tupleVIFam ds =
  VIDistFam
  { viDistDim = foldrADT (viDistDim . getCompose) (+) 0 ds
  , viDistSample = traverseADT (viDistSample . getCompose) ds
  , viDistEntropy =
      foldrADT (viDistEntropy . getCompose)
      (\m1 m2 -> (+) <$> m1 <*> m2) (return 0) ds
  , viDistScaledGradPDF =
      (\scale tup ->
        foldrADT getConst (>>) (return ()) $
        mapTuple2 (\(Compose d) a ->
                    Const $ viDistScaledGradPDF d scale a) ds tup)
  , viDistInit = foldrADT (viDistInit . getCompose) (>>) (return ()) ds
  , viDistGrowParams =
    foldrADT (viDistGrowParams . getCompose) (>>) (return ()) ds
  , viDistPP =
    PP.tupled <$> sequence (ctorArgsADT (viDistPP . getCompose) ds)
  }

-- | Transform a distribution family over one type to another type using a
-- volume-preserving isomorphism. A volume-preserving map is one that does not
-- squeeze any objects closer together or move them farther apart; the technical
-- definition is that it preserves the measures of all sets with respect to the
-- reference measure on the two spaces.
xformVIDistFam :: (a -> b) -> (b -> a) -> VIDistFam a -> VIDistFam b
xformVIDistFam f_to f_from (VIDistFam {..}) =
  VIDistFam
  {
    viDistSample = fmap f_to $ viDistSample,
    viDistScaledGradPDF = (\scale a -> viDistScaledGradPDF scale (f_from a)),
    ..
  }

-- | Map a vector of distribution families to a distribution family of vectors
vecDistVIFam :: (SVGen.Vector f a, SVGen.Vector f (VIDistFam a)) =>
                f (VIDistFam a) -> VIDistFam (f a)
vecDistVIFam ds =
  VIDistFam
  { viDistDim = SVGen.foldl' (\dim d -> dim + viDistDim d) 0 ds
  , viDistSample = SVGen.mapM viDistSample ds
  , viDistEntropy = SVGen.foldM' (\e d -> (e +) <$> viDistEntropy d) 0 ds
  , viDistScaledGradPDF =
    (\scale v ->
      if SVGen.length v == SVGen.length ds then
        SVGen.zipWithM_ (\d x -> viDistScaledGradPDF d scale x) ds v
      else
        error "vecDist distribution: wrong size vector!")
  , viDistInit = SVGen.mapM_ viDistInit ds
  , viDistGrowParams = SVGen.mapM_ viDistGrowParams ds
  , viDistPP =
    do pps <- mapM viDistPP $ SVGen.toList ds
       return (PP.text "vecDist" <+> PP.list pps)
  }

-- | The distribution family over vectors with a given length whose elements are
-- drawn IID from the supplied distribution family
vecIIDVIFam :: SVGen.Vector f a => VIDim -> VIDistFam a -> VIDistFam (f a)
vecIIDVIFam len d =
  VIDistFam
  { viDistDim = len * viDistDim d
  , viDistSample =
    do asgn <- ask
       SVGen.replicateM (evalVIDim len asgn) (viDistSample d)
  , viDistEntropy =
    do asgn <- ask
       entropies <- replicateM (evalVIDim len asgn) (viDistEntropy d)
       return $ sum entropies
  , viDistScaledGradPDF =
    (\scale v ->
      do asgn <- ask
         if SVGen.length v == evalVIDim len asgn then
           SVGen.forM_ v (viDistScaledGradPDF d scale)
           else
           error "IID distribution: wrong size vector!")
  , viDistInit =
    do asgn <- ask
       replicateM_ (evalVIDim len asgn) (viDistInit d)
  , viDistGrowParams =
    do (old_asgn, new_asgn) <- ask
       replicateM_ (evalVIDim len old_asgn) (viDistGrowParams d)
       g <- lift $ lift $ lift $ nthGenIO 0
       let num_new_elems = evalVIDim len new_asgn - evalVIDim len old_asgn
       replicateM_ num_new_elems $
         do new_params <- getMutParams (evalVIDim (viDistDim d) new_asgn)
            liftIO $ runInitM (viDistInit d) g new_asgn new_params
  , viDistPP =
    do asgn <- ask
       let n = evalVIDim len asgn
       pps <- replicateM n (viDistPP d)
       return (PP.text ("IID(" ++ show n ++ ")") <+> PP.list pps)
  }


----------------------------------------------------------------------
-- * Distribution Approximator Expressions
----------------------------------------------------------------------

-- | An "expression" for building up a family of distributions, which keeps
-- track of how many dimensionality variables we have used so far and also a
-- list of the data file names to be used by 'readJSONVIDistFamExpr'
newtype VIDistFamExpr a =
  VIDistFamExpr { runVIDistFamExpr ::
                    StateT (VIDimVar, [String]) IO (VIDistFam a) }

-- | Evaluate a distribution family expression into a distribution family
evalVIDistFamExpr :: [String] -> VIDistFamExpr a -> IO (VIDistFam a)
evalVIDistFamExpr files (VIDistFamExpr m) = evalStateT m (VIDimVar 0, files)

entropyNaNProtect :: String -> DiffFun -> DiffFun
entropyNaNProtect s f ps =
  let ret = f ps in
  if isNaN ret then
    error ("NaN entropy for distribution " ++ s ++ ", params = " ++ show ps)
  else
    ret

-- | Build a distribution family expression for a "simple" distribution, meaning
-- it is not a composite of multiple distributions on sub-components.  Such a
-- distribution is defined by a dimensionality expression, a sampling function,
-- and differentiable functions for the entropy and log PDF.
simpleVIFamExpr :: String -> VIDim -> (Params -> MWCRandM a) -> DiffFun ->
                   (a -> DiffFun) -> (VIDimAsgn -> MWCRandM [Double]) ->
                   VIDistFamExpr a
simpleVIFamExpr nm dim sampleFun entropyFun pdfFun initFun =
  VIDistFamExpr $ return $
  simpleVIFam nm dim sampleFun (entropyNaNProtect nm entropyFun) pdfFun initFun

-- | The constant distribution (also known as the delta distribution), that
-- returns a single value with unit probability
deltaVIFamExpr :: (Eq a, GrappaShow a) => a -> VIDistFamExpr a
deltaVIFamExpr a =
  simpleVIFamExpr ("Delta(" ++ grappaShow a ++ ")")
  0 (\_ -> return a) (\_ -> 0)
  (\x _ -> if x == a then 0 else log 0)
  (const $ return [])

-- | Build a distribution family expression for the normal distribution, where
-- we use absolute value of @sigma@ to map it to the non-negative reals
normalVIFamExpr :: VIDistFamExpr R
normalVIFamExpr =
  simpleVIFamExpr "Normal" 2 (\ps -> mwcNormal (ps SV.! 0) (abs (ps SV.! 1)))
  (\ps ->  0.5 * (1 + log (2 * pi) + log ((ps V.! 1) * (ps V.! 1))))
  (\x ps -> Log.ln $ normalDensityUnchecked (ps V.! 0) (abs (ps V.! 1)) (fromDouble x))
  (\_ ->
    -- Init mu from the standard normal and sigma from the inverse gamma
    do mu <- random MWC.standard
       inv_sigma_sq <- mwcGamma 1 1
       let sigma = 1 / sqrt inv_sigma_sq
       return [mu,sigma])

-- | Build a distribution family expression for the uniform distribution over
-- the range @(min a b, max a b]@
uniformVIFamExpr :: VIDistFamExpr R
uniformVIFamExpr =
  simpleVIFamExpr "Uniform" 2 (\ps -> mwcUniform (ps SV.! 0) (ps SV.! 1))
  (\ps -> log $ abs (ps V.! 1 - ps V.! 0))
  (\x ps ->
    if min (ps V.! 0) (ps V.! 1) < fromDouble x
       && fromDouble x <= max (ps V.! 0) (ps V.! 1) then
      log $ abs (ps V.! 1 - ps V.! 0)
    else log 0)
  (\_ ->
    -- Initialize to a sub-interval of the unit interval by setting lower =
    -- uniform(0,1) and upper = lower + uniform(0,1) * (1 - lower)
    do lower <- mwcUniform 0 1
       upper_nonnorm <- mwcUniform 0 1
       let upper = lower + upper_nonnorm * (1 - lower)
       return [lower, upper])

-- | Build a distribution family expression for the categorical distribution
-- over @[0,..,n-1]@ with relative probabilities @[a1/a,..,an/a]@, where each
-- @ai@ is the absolute value of the @i@th parameter and @a@ is the sum of the
-- @ai@s. The special case that @n=0@ is treated like @n=1@, meaning it always
-- returns @0@.
categoricalVIFamExpr :: VIDim -> VIDistFamExpr Int
categoricalVIFamExpr dim =
  simpleVIFamExpr "Categorical" dim
  (\ps ->
    -- NOTE: MWC.categorical normalizes the weights for us
    random $ MWC.categorical $ SV.map abs ps)
  (\ps ->
    let ps' = V.map abs ps
        p_sum = V.sum ps' in
    V.sum $ V.map (\p -> (p / p_sum) * log (p / p_sum)) ps')
  (\x ps ->
    let ps' = V.map abs ps
        p_sum = V.sum ps'
        n = V.length ps in
    if n == 0 && x == 0 then 1 else
      if x < 0 || x >= n then 0 else
        log ((ps' V.! x) / p_sum))
  (\asgn ->
    -- Initialize the probabilities from a Dirichlet distribution
    let n = evalVIDim dim asgn in
    if n == 0 then return [] else
      mwcDirichlet (replicate n 1))

-- | Build a distribution family expression for the gamma distribution, where
-- we use absolute value of @k@ and @theta@ to them to the non-negative reals
gammaVIFamExpr :: VIDistFamExpr R
gammaVIFamExpr =
  simpleVIFamExpr "Gamma" 2 (\ps -> mwcGamma (abs (ps SV.! 0)) (abs (ps SV.! 1)))
  (\ps ->
    let k = abs (ps SV.! 0)
        theta = abs (ps SV.! 1) in
    k + log theta + logGamma k + (1-k) * digamma k)
  (\x ps ->
    Log.ln $
    gammaDensityUnchecked (abs (ps V.! 0)) (abs (ps V.! 1)) (fromDouble x))
  (\_ ->
    -- Initialize k and theta from exponentials (because their actual conjugate
    -- priors are messy and I'm too busy for that)
    do k <- mwcExponential 1
       theta <- mwcExponential 1
       return [k,theta])

-- | Build a distribution family expression for the gamma distribution over
-- probabilities, i.e., in log space, where the @k@ and @theta@ parameters are
-- also in log space
gammaProbVIFamExpr :: VIDistFamExpr Prob
gammaProbVIFamExpr =
  simpleVIFamExpr "GammaProb" 2
  (\ps -> Prob <$> mwcGammaLogLog (Log.Exp (ps SV.! 0)) (Log.Exp (ps SV.! 1)))
  (\ps ->
    let k = exp (ps SV.! 0)
        log_theta = ps SV.! 1 in
    k + log_theta + logGamma k + (1-k) * digamma k)
  (\x ps ->
    Log.ln $
    gammaDensityUnchecked (exp (ps V.! 0)) (exp (ps V.! 1))
    (fromDouble $ probToLogR x))
  (\_ ->
    -- Initialize (exp k) and (exp theta) from the exponential distribution, in
    -- keeping with the initialization for gammaVIFamExpr, above. NOTE: this
    -- kind of sucks, because we are just taking log (log uniform(0,1)), and
    -- taking two logarithms in a row probably loses a lot of precision.
    do exp_k <- mwcExponential 1
       exp_theta <- mwcExponential 1
       return [log exp_k, log exp_theta])

-- | Build a distribution family expression for the beta distribution, where
-- we use absolute value of @alpha@ and @beta@ to keep them non-negative
betaVIFamExpr :: VIDistFamExpr R
betaVIFamExpr =
  simpleVIFamExpr "Beta" 2 (\ps -> mwcBeta (abs (ps SV.! 0)) (abs (ps SV.! 1)))
  (\ps ->
    let alpha = abs (ps SV.! 0)
        beta = abs (ps SV.! 1) in
    logGamma alpha + logGamma beta - logGamma (alpha + beta)
    + (alpha + beta - 2) * digamma (alpha + beta)
    - (alpha - 1) * digamma alpha - (beta - 1) * digamma beta)
  (\x ps ->
    Log.ln $
    betaDensityUnchecked (abs (ps V.! 0)) (abs (ps V.! 1)) (fromDouble x))
  (\_ ->
    -- Initialize alpha and beta from the exponential distribution, because why
    -- not? And because, as Wikipedia says (for the Dirichlet distribution,
    -- which is similar), "In the published literature there is no practical
    -- algorithm to efficiently generate samples from" the conjugate prior.
    do alpha <- mwcExponential 1
       beta <- mwcExponential 1
       return [alpha,beta])

-- | Build a distribution family expression for the beta distribution over
-- probabilities, i.e., in log space, where the @alpha@ and @beta@ parameters
-- are also in log space
betaProbVIFamExpr :: VIDistFamExpr Prob
betaProbVIFamExpr =
  simpleVIFamExpr "BetaProb" 2
  (\ps -> Prob <$> mwcBetaLogLog (Log.Exp (ps SV.! 0)) (Log.Exp (ps SV.! 1)))
  (\ps ->
    let alpha = exp (ps SV.! 0)
        beta = exp (ps SV.! 1) in
    logGamma alpha + logGamma beta - logGamma (alpha + beta)
    + (alpha + beta - 2) * digamma (alpha + beta)
    - (alpha - 1) * digamma alpha - (beta - 1) * digamma beta)
  (\x ps ->
    Log.ln $
    betaDensityLog (exp (ps V.! 0)) (exp (ps V.! 1))
    (fmap fromDouble $ fromProb x))
  (\_ ->
    -- Initialize (exp alpha) and (exp beta) from the exponential distribution,
    -- in keeping with the initialization for betaVIFamExpr, above. NOTE: this
    -- kind of sucks, because we are just taking log (log uniform(0,1)), and
    -- taking two logarithms in a row probably loses a lot of precision.
    do exp_alpha <- mwcExponential 1
       exp_beta <- mwcExponential 1
       return [log exp_alpha, log exp_beta])

-- | Build a distribution family for the dirichlet distribution, where the
-- alphas are in log space, so they can never be negative and so that the
-- optimization can do better at picking very small alphas
dirichletVIFamExpr :: VIDim -> VIDistFamExpr [R]
dirichletVIFamExpr dim =
  simpleVIFamExpr "Dirichlet" dim
  (\ps -> mwcDirichlet (SV.toList $ SV.map exp ps))
  (\ps ->
    let alphas = SV.toList $ SV.map exp ps
        k = fromIntegral $ SV.length ps
        alpha0 = sum alphas in
    sum (map logGamma alphas) - logGamma alpha0
    + (alpha0 - k) * digamma alpha0
    - sum (flip map alphas $ \alpha -> (alpha - 1) * digamma alpha))
  (\x ps -> Log.ln $
            dirichletDensity (SV.toList $ SV.map exp ps) (map fromDouble x))
  (\asgn ->
    -- Initialize alphas from the exponential distribution, because why not? And
    -- because, as Wikipedia says, "In the published literature there is no
    -- practical algorithm to efficiently generate samples from" the conjugate
    -- prior.
    replicateM (evalVIDim dim asgn) (mwcExponential 1))

-- | Build a distribution family for the dirichlet distribution over
-- probabilities, i.e., over lists of reals in log space. The alphas are in log
-- space, so they can never be negative and so that the optimization can do
-- better at picking very small alphas
dirichletProbVIFamExpr :: VIDim -> VIDistFamExpr [Prob]
dirichletProbVIFamExpr dim =
  simpleVIFamExpr "DirichletProb" dim
  (\ps -> map Prob <$> mwcDirichletLog (SV.toList $ SV.map exp ps))
  (\ps ->
    let alphas = SV.toList $ SV.map exp ps
        k = fromIntegral $ SV.length ps
        alpha0 = sum alphas in
    sum (map logGamma alphas) - logGamma alpha0
    + (alpha0 - k) * digamma alpha0
    - sum (flip map alphas $ \alpha -> (alpha - 1) * digamma alpha))
  (\x ps -> Log.ln $
            dirichletDensityLog (SV.toList $ SV.map exp ps)
            (map (fmap fromDouble . fromProb) x))
  (\asgn ->
    -- Initialize (exp alphas) from the exponential distribution, because why
    -- not? And because, as Wikipedia says, "In the published literature there
    -- is no practical algorithm to efficiently generate samples from" the
    -- conjugate prior. NOTE: this kind of sucks, because we are just taking log
    -- (log uniform(0,1)), and taking two logarithms in a row probably loses a
    -- lot of precision.
    map log <$> replicateM (evalVIDim dim asgn) (mwcExponential 1))

-- | Bind a fresh dimensionality variable in a distribution family expression
bindVIDimFamExpr :: (VIDim -> VIDistFamExpr a) -> VIDistFamExpr a
bindVIDimFamExpr f =
  VIDistFamExpr $ do
  (v,files) <- get
  put $ (nextVar v, files)
  runVIDistFamExpr $ f (varVIDim v)

-- | Build a distribution family expression for a tuple from a tuple of
-- distribution family expressions
tupleVIFamExpr :: TupleF ts (Compose VIDistFamExpr f) (ADT (TupleF ts)) ->
                  VIDistFamExpr (TupleF ts f (ADT (TupleF ts)))
tupleVIFamExpr d_exprs =
  VIDistFamExpr $ fmap tupleVIFam $
  traverseADT ((Compose <$>) . runVIDistFamExpr . getCompose) d_exprs

-- | Transform a distribution family expression over one type to another type
-- using a volume-preserving isomorphism; see 'xformVIDistFam'.
xformVIDistFamExpr :: (a -> b) -> (b -> a) -> VIDistFamExpr a -> VIDistFamExpr b
xformVIDistFamExpr f_to f_from expr =
  VIDistFamExpr (xformVIDistFam f_to f_from <$> runVIDistFamExpr expr)

-- | The distribution family expression over vectors with a given length whose
-- elements are drawn IID from the supplied distribution family expression
vecIIDVIFamExpr :: VIDim -> VIDistFamExpr a -> VIDistFamExpr (Vector a)
vecIIDVIFamExpr len d_expr =
  VIDistFamExpr (vecIIDVIFam len <$> runVIDistFamExpr d_expr)

-- | Map a vector of distribution family expressions to a distribution family
-- expression over vectors
vecDistVIFamExpr :: (SVGen.Vector f a, SVGen.Vector f (VIDistFam a),
                     SVGen.Vector f (VIDistFamExpr a)) =>
                    f (VIDistFamExpr a) -> VIDistFamExpr (f a)
vecDistVIFamExpr d_exprs =
  VIDistFamExpr (vecDistVIFam <$> SVGen.mapM runVIDistFamExpr d_exprs)

-- | The distribution family expression over lists with a given length whose
-- elements are drawn IID from the supplied distribution family expression
iidVIFamExpr :: VIDim -> VIDistFamExpr a -> VIDistFamExpr [a]
iidVIFamExpr len d_expr =
  xformVIDistFamExpr V.toList V.fromList $ vecIIDVIFamExpr len d_expr

-- | The distribution family expression over lists with a given length whose
-- elements are drawn IID from the supplied distribution family expression
iidPVVIFamExpr :: VIDim -> VIDistFamExpr Prob -> VIDistFamExpr ProbVector
iidPVVIFamExpr len d_expr =
  xformVIDistFamExpr ProbVector unProbVector $
  VIDistFamExpr (vecIIDVIFam len <$> runVIDistFamExpr
                 (xformVIDistFamExpr probToLogR logRToProb d_expr))

-- | This distribution family reads an input of type @a@ from @stdin@ as a JSON
-- file and then passes that input to the supplied function to build a
-- distribution family of type @b@
mapJSONVIDistFamExpr :: FromJSON a => (a -> VIDistFamExpr b) -> VIDistFamExpr b
mapJSONVIDistFamExpr f =
  VIDistFamExpr $
  do (v,files) <- get
     let (file, files') =
           if length files == 0 then
             error "mapJSONVIDistFamExpr: not enough data files specified"
           else (head files, tail files)
     put (v, files')
     a <- liftIO $ readJSONfile file
     runVIDistFamExpr $ f a

-- | This distribution family is a delta distribution (i.e., one that always
-- returns the same value, like 'deltaVIFamExpr') that reads its input from
-- stdin as a JSON file
readJSONVIDistFamExpr :: (Eq a, GrappaShow a, FromJSON a) => VIDistFamExpr a
readJSONVIDistFamExpr = mapJSONVIDistFamExpr deltaVIFamExpr


----------------------------------------------------------------------
-- * Variational Inference, Yay!
----------------------------------------------------------------------

-- | A PVIE model is a dimensionaltiy variable assignment + model parameters
data PVIEModel =
  PVIEModel { pvieModelAsgn :: VIDimAsgn,
              pvieModelParams :: Params }
  deriving Generic

instance FromJSON PVIEModel where

instance ToJSON PVIEModel where
  toEncoding = genericToEncoding defaultOptions

readPVIEModel :: MWC.GenIO -> VIDistFam a -> String -> IO PVIEModel
readPVIEModel g d filename =
  doesFileExist filename >>= \ex ->
  if ex then
    -- If filename exists, then read it
    readJSONfile filename
  else
    -- Otherwise, start with 0 for all dimensionality variables, and
    -- initialize all params to 1
    do let asgn = zeroAsgn $ viDimFirstUnusedVar $ viDistDim d
       mut_params <- SMV.new (evalVIDim (viDistDim d) asgn)
       runInitM (viDistInit d) g asgn mut_params
       params <- SV.freeze mut_params
       return $ PVIEModel asgn params


-- | The PVIE modes: training and evaluation
data PVIEMode = PVIETrainMode | PVIEEvalMode

-- | The PVIE command-line options
data PVIEOpts =
  PVIEOpts {
  pvieModelFile :: String,
  pvieDataFiles :: [String],
  pvieMode :: PVIEMode,
  pvieVerbosity :: Int,
  pvieDebugTruncate :: Maybe Int,
  pvieGD :: Bool
  }

-- | Parser for PVIE command-line options
pvieOptsParser :: Parser PVIEOpts
pvieOptsParser =
  PVIEOpts
  <$> (strOption (long "model"
                  <> short 'm'
                  <> metavar "MODEL"
                  <> help "Model file"
                  <> value "-"
                  <> showDefault))
  <*> many (strOption (long "data"
                       <> short 'd'
                       <> metavar "DATAFILE"
                       <> help "Data file"))
  <*> (flag' PVIETrainMode (long "train" <> short 't'
                            <> help "Specifies training mode")
       <|>
       flag' PVIEEvalMode (long "eval" <> short 'e'
                            <> help "Specifies evaluation mode"))
  <*> (option auto (long "verbosity" <> short 'v'
                    <> help "Verbosity level for debugging"
                    <> showDefault <> value 0 <> metavar "VERBOSITY"))
  <*> (option (Just <$> auto)
       (long "truncate" <> short 'T'
        <> help "Truncate length for debugging strings"
        <> showDefault <> value Nothing <> metavar "TRUNCATE"))
  <*> (flag False True
       (long "gd" <>
        help "Use gradient descent instead of BFGS to optimize (only meaningful in training mode)"))

-- | Parse the command-line options
parsePVIEOpts :: IO PVIEOpts
parsePVIEOpts = execParser (info (pvieOptsParser <**> helper)
                            (fullDesc <>
                             progDesc "FIXME: description of PVIE"))

debugTruncate :: PVIEOpts -> String -> String
debugTruncate opts s
  | Just l <- pvieDebugTruncate opts
  , length s >= l = take l s ++ " ..."
debugTruncate _ s = s

-- | Print debugging info if the verbosity level is @>= level@
debugM :: PVIEOpts -> Int -> String -> IO ()
debugM opts level s
  | pvieVerbosity opts >= level = traceM (debugTruncate opts s)
debugM _ _ _ = return ()

-- | Find the parameters that /minimize/ the given differentiable function
optimize :: PVIEOpts -> (Params -> MutParams -> IO Double) ->
            MutParams -> IO Double
optimize opts f mut_params =
  do let len = SMV.length mut_params
     let meth = if pvieGD opts then SteepestDescent else VectorBFGS2
     params <- SV.freeze mut_params
     let eval_f ps =
           unsafePerformIO $
           do debugM opts 2 ("neg_elbo: params = " ++ show ps)
              grad <- SMV.replicate len 0
              ret <- f ps grad
              debugM opts 2 ("surprisal = " ++ show ret)
              return ret
     let grad_f ps =
           unsafePerformIO $
           do debugM opts 2 ("neg_elbo_grad: params = " ++ show ps)
              grad <- SMV.replicate len 0
              _ <- f ps grad
              ret <- SV.unsafeFreeze grad
              debugM opts 2 ("grad = " ++ show ret)
              return ret
     let (opt_params,_) =
           minimizeVD meth 0.0001 1000 1 0.1 eval_f grad_f params
     SV.copy mut_params opt_params
     return $ eval_f opt_params

-- FIXME HERE: make pvie_epsilon and num_samples into command-line options

-- | The amount that PVIE has to improve in an interation to seem "better"
pvie_epsilon :: Double
pvie_epsilon = 1.0e-6

-- | FIXME: make this be a command-line option somehow!
num_samples :: Int
num_samples = 1000

-- | The negative infinity value
negInfinity :: Double
negInfinity = log 0

-- | Test if a 'Double' is (positive or negative) infinity or NaN
isInfiniteOrNaN :: Double -> Bool
isInfiniteOrNaN x = isInfinite x || isNaN x

-- | Compute the negative Evidence Lower BOund (or ELBO) and its gradient
neg_elbo_with_grad :: GrappaShow a => PVIEOpts -> MWC.GenIO ->
                      VIDistFam a -> (a -> Double) -> VIDimAsgn ->
                      (Params -> MutParams -> IO Double)
neg_elbo_with_grad opts g d log_p asgn params grad =
  do ret <- elbo_with_grad opts g d log_p asgn params grad
     forM_ [0 .. (SMV.length grad)-1] (SMV.modify grad negate)
     return (-ret)

-- | Compute the Evidence Lower BOund (or ELBO) and its gradient
elbo_with_grad :: GrappaShow a => PVIEOpts -> MWC.GenIO ->
                  VIDistFam a -> (a -> Double) -> VIDimAsgn ->
                  (Params -> MutParams -> IO Double)
elbo_with_grad opts g d log_p asgn params grad =
  (replicateM num_samples $
   do s <- runSamplingM (viDistSample d) g asgn params
      return (s, log_p s)) >>= \samples_log_ps ->
  case find (isInfiniteOrNaN . snd) samples_log_ps of
    Just (bad_samp, p) ->
      -- If any of our samples have 0 probability in our model (i.e., from
      -- log_p), the elbo is -infinity, and the gradient is undefined. However,
      -- knowing our optimization algorithm, we cheat, and tell it that the
      -- gradient is just the sum of the negatives of the gradients of d at
      -- those 0 probability samples. That way, our optimization algorithm will
      -- keep trying to reduce the probabilities of generating bad samples until
      -- it finally succeeds. Note that we still return -infinity as the value.
      do debugM opts 3 ((if isNaN p then "NaN" else
                           if p < 0 then "Zero-probability"
                           else "Infinite (?) probability") ++
                        " sample: " ++ grappaShow bad_samp)
         forM_ samples_log_ps $ \(samp, samp_p) ->
           when (isInfiniteOrNaN samp_p) $
           runParamsGradM (viDistScaledGradPDF d (-1e9) samp) asgn params grad
         return negInfinity
    _ ->
      do let n = fromIntegral num_samples
         entr <- runParamsGradM (viDistEntropy d) asgn params grad
         debugM opts 2 ("Entropy: " ++ show entr)
         entr_grad <- SV.freeze grad
         debugM opts 3 ("Entropy grad: " ++ show entr_grad)
         forM_ samples_log_ps $ \(samp, p) ->
           runParamsGradM (viDistScaledGradPDF d (p / n) samp) asgn params grad
         -- grad_const <- SV.unsafeFreeze grad
         -- traceM ("grad = " ++ show grad_const)
         let ret = entr + (1/n) * sum (map snd samples_log_ps)
         -- traceM ("surprisal = " ++ show ret)
         debugM opts 4 ("Sample 0: " ++ grappaShow (fst $ head samples_log_ps))
         return ret

-- | The main entrypoint for the PVIE engine
pvie_main :: GrappaShow a => VIDistFamExpr a -> (a -> Double) -> IO ()
pvie_main dist_expr log_p =
  do opts <- parsePVIEOpts
     dist_fam <- evalVIDistFamExpr (pvieDataFiles opts) dist_expr
     case pvieMode opts of
       PVIETrainMode ->
         do (model@(PVIEModel asgn params), val) <-
              pvie_train opts dist_fam log_p
            pp <- applyPPFun (viDistPP dist_fam) asgn params
            debugM opts 1 ("Final model:\n" ++ show pp)
            debugM opts 1 ("Surprisal score: " ++ show val)
            writeJSONfile (pvieModelFile opts) model
       PVIEEvalMode ->
         do val <- pvie_eval opts dist_fam log_p
            putStrLn ("Surprisal score: " ++ show val)

-- | The main entrypoint for the PVIE engine with anomaly score
pvie_anom_main :: GrappaShow a => VIDistFamExpr a -> (a -> Double) ->
                  (a -> Prob) -> IO ()
pvie_anom_main dist_expr log_p anom_score =
  do opts <- parsePVIEOpts
     dist_fam <- evalVIDistFamExpr (pvieDataFiles opts) dist_expr
     case pvieMode opts of
       PVIETrainMode ->
         do (model@(PVIEModel asgn params), val) <-
              pvie_train opts dist_fam log_p
            pp <- applyPPFun (viDistPP dist_fam) asgn params
            debugM opts 1 ("Final model:\n" ++ show pp)
            debugM opts 1 ("Surprisal score: " ++ show val)
            writeJSONfile (pvieModelFile opts) model
       PVIEEvalMode ->
         do score <- pvie_eval_anom opts dist_fam anom_score
            putStrLn $ show (1 - min 1 (probToR score))

-- | The PVIE eval mode
pvie_eval :: GrappaShow a => PVIEOpts -> VIDistFam a -> (a -> Double) ->
             IO Double
pvie_eval opts d log_p =
  do PVIEModel asgn params <- readJSONfile $ pvieModelFile opts
     g <- MWC.createSystemRandom
     grad <- SMV.new (evalVIDim (viDistDim d) asgn)
     val <- neg_elbo_with_grad opts g d log_p asgn params grad
     return val

-- | Evaluate the anomaly score, which is the average over @N@ samples of the
-- supplied anomaly score function applied to each sample
pvie_eval_anom :: GrappaShow a => PVIEOpts -> VIDistFam a -> (a -> Prob) ->
                  IO Prob
pvie_eval_anom opts d anom_score =
  do PVIEModel asgn params <- readJSONfile $ pvieModelFile opts
     g <- MWC.createSystemRandom
     anom_scores <-
       replicateM num_samples $
       do samp <- runSamplingM (viDistSample d) g asgn params
          return (probToLogR $ anom_score samp)
     return $ logRToProb (sum anom_scores / fromIntegral num_samples)

-- | The PVIE training mode
pvie_train :: GrappaShow a => PVIEOpts -> VIDistFam a -> (a -> Double) ->
              IO (PVIEModel, Double)
pvie_train opts d log_p = init_pvie where

  -- Initialize PVIE and start it running
  init_pvie :: IO (PVIEModel, Double)
  init_pvie = do
    g <- MWC.createSystemRandom
    PVIEModel asgn params <- readPVIEModel g d (pvieModelFile opts)
    mut_params <- SV.unsafeThaw params
    -- Generate the initial value to try to beat
    val <- optimize opts (neg_elbo_with_grad opts g d log_p asgn) mut_params
    params' <- SV.unsafeFreeze mut_params
    -- If there are no dimensionality variables in our distribution family, then
    -- there is nothing to increment, so we are done
    if viDimFirstUnusedVar (viDistDim d) == zeroVar then
      outer g asgn params' val False
      else
      -- Perform the first iteration of optimizing the dimensionality variables
      outer g asgn params' val True

  -- The main outer loop
  outer :: MWC.GenIO -> VIDimAsgn -> Params -> Double -> Bool ->
           IO (PVIEModel, Double)
  outer _ asgn params last_val False =
    -- If our last iteration of the outer loop did not improve, we are done, and
    -- return the current assignment, parameters, and value
    return (PVIEModel asgn params, last_val)

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
           MutParams -> Bool -> IO (PVIEModel, Double)
  inner g asgn last_params last_val next_var _ improved
    | next_var == viDimFirstUnusedVar (viDistDim d)
    = outer g asgn last_params last_val improved

  inner g asgn last_params last_val next_var scratch improved = do
    -- The next assignment we will try = increment next_var
    let new_asgn = incrAsgn next_var asgn
    -- Copy our current best parameters into our scratch area
    runGrowM (viDistGrowParams d) g asgn new_asgn last_params scratch
    -- Optimize those parameters
    new_val <- optimize opts (neg_elbo_with_grad opts g d log_p asgn) scratch
    -- Test how much we improved
    if last_val - new_val >= pvie_epsilon then
      -- If we did improve, swap last_params and scratch, then iterate
      do new_params <- SV.unsafeFreeze scratch
         new_scratch <- SV.unsafeThaw last_params
         inner g new_asgn new_params new_val (nextVar next_var) new_scratch True
      else
      -- Otherwise, keep the same assignment, params, and scratch
      inner g asgn last_params last_val (nextVar next_var) scratch improved
