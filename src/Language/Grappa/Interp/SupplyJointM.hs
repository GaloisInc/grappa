{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.Grappa.Interp.SupplyJointM (
  SupplyJointM(..), SJRepr, SJReprF, SupplyJointCtx,
  logProbOf, logGradientOf, outputOf
  ) where

import Control.Monad.Reader
import Control.Monad.ST
import Data.STRef

import qualified Data.Vector as V

import qualified Numeric.AD.Mode.Reverse as ADR
import qualified Numeric.AD.Internal.Reverse as ADR (Tape)
import qualified Data.Reflection as ADR (Reifies)

import Language.Grappa.Distribution
import Language.Grappa.Interp
import Language.Grappa.GrappaInternals
import Language.Grappa.Interp.Supply
import Language.Grappa.Interp.StandardHORepr

import qualified Numeric.Log as Log


----------------------------------------------------------------------
-- * A Monad for Computing Joint Probability from a 'Supply'
----------------------------------------------------------------------

-- | The state used by 'SupplyJointM'
data SupplyJointState supply s =
  SupplyJointState { sjSupply :: !(STRef s supply)
                                 -- ^ The current supply of "random values"
                   , sjProb   :: !(STRef s (Log.Log (SupplyReal supply)))
                                 -- ^ The cumulative joint probability so far
                   }


-- | A monad for computing joint probability from a 'Supply'
newtype SupplyJointM supply a =
  SupplyJointM { unSupplyJointM ::
                   forall s. ReaderT (SupplyJointState supply s) (ST s) a }

instance Functor (SupplyJointM supply) where
  fmap f m = m >>= return . f

instance Applicative (SupplyJointM supply) where
  pure = return
  (<*>) = ap

instance Monad (SupplyJointM supply) where
  return x = SupplyJointM $ return x
  (SupplyJointM m) >>= f =
    SupplyJointM (m >>= unSupplyJointM . f)

-- | Helper to apply a supply-updating function to the current supply
applySupplyFun :: (supply -> (a, supply)) -> SupplyJointM supply a
applySupplyFun supplyFun =
  SupplyJointM $ do SupplyJointState { .. } <- ask
                    supply <- lift $ readSTRef sjSupply
                    let (a, supply') = supplyFun supply
                    lift $ writeSTRef sjSupply supply'
                    return a

-- | Supply the next continuous value in the 'SupplyJointM' monad
supplyRealM :: Supply supply => SupplyJointM supply (SupplyReal supply)
supplyRealM = applySupplyFun supplyReal

-- | Supply the next @n@ continuous values in the 'SupplyJointM' monad
supplyRealsM :: Supply supply => Int ->
                SupplyJointM supply [SupplyReal supply]
supplyRealsM n = applySupplyFun $ flip supplyReals n

-- | Supply the next discrete value in the 'SupplyJointM' monad
supplyIntM :: Supply supply => SupplyJointM supply (SupplyInt supply)
supplyIntM = applySupplyFun supplyInt

-- | Update the joint probability in the 'SupplyJointM' monad
updateJointProbM :: (Log.Precise (SupplyReal supply),
                     RealFloat (SupplyReal supply)) =>
                    Log.Log (SupplyReal supply) -> SupplyJointM supply ()
updateJointProbM p =
  SupplyJointM $ do SupplyJointState { .. } <- ask
                    lift $ modifySTRef' sjProb (* p)


----------------------------------------------------------------------
-- * Run Methods for 'SupplyJointM'
----------------------------------------------------------------------

-- | Typeclass context needed to use 'SupplyJointM'
type SupplyJointCtx supply r i =
  (Supply supply, SupplyInt supply ~ i, SupplyReal supply ~ r,
   Show i, Eq i, Integral i, Show r, Ord r, Log.Precise r, RealFloat r,
   EmbedVarData Double r, EmbedVarData Int i)

-- | Run a 'SupplyJointM' computation
runSupplyJointM :: SupplyJointCtx supply r i =>
                   SupplyJointM supply a -> supply -> (Log.Log r, a)
runSupplyJointM m supply =
  runST $
  do sjSupply <- newSTRef supply
     sjProb <- newSTRef 1
     a <- runReaderT (unSupplyJointM m) (SupplyJointState { .. })
     prob <- readSTRef sjProb
     return (prob, a)

-- | Run a 'SupplyJointM' computation inside 'IO'
{-
runSupplyJointMIO :: SupplyJointCtx supply r i =>
                     SupplyJointM supply RealWorld a -> supply ->
                     IO (Log.Log r, a)
runSupplyJointMIO (SupplyJointM m) supply =
  stToIO $
  do sjSupply <- newSTRef supply
     sjProb <- newSTRef 1
     a <- runReaderT m (SupplyJointState { .. })
     prob <- readSTRef sjProb
     return (prob, a)
-}

-- | Shorthand for a 'StandardHORepr' using 'SupplyJointM'
type SJRepr supply =
  StandardHORepr (SupplyJointM supply) (SupplyReal supply) (SupplyInt supply)

-- | Shorthand for a 'StandardHOReprF' using 'SupplyJointM'
type SJReprF supply a =
  StandardHOReprF (SupplyJointM supply) (SupplyReal supply) (SupplyInt supply) a

-- | Get the output of a model given a supply, using 'SupplyJointM'
outputOf :: SupplyJointCtx supply r i =>
            GStmt (SJRepr supply) a -> supply -> SJReprF supply a
outputOf stmt supply = snd $ runSupplyJointM (unGStmt stmt) supply

-- | Get the log joint probability of a model given a supply, using
-- 'SupplyJointM'
logProbOf :: SupplyJointCtx supply Double i =>
             GStmt (SJRepr supply) a -> supply -> Prob
logProbOf stmt supply =
  Prob $ fst $ runSupplyJointM (void $ unGStmt stmt) supply

-- | Get the gradient of the log probability of a model, using 'SupplyJointM'
logGradientOf :: (forall s. ADR.Reifies s ADR.Tape =>
                  GStmt (SJRepr (VectorSupply (ADR.Reverse s Double) Int)) a) ->
                 V.Vector Int -> V.Vector Double ->
                 V.Vector Double
logGradientOf stmt is rs =
  ADR.grad (\grad_rs ->
             Log.ln $ fst $
             runSupplyJointM (void $ unGStmt stmt) (VectorSupply grad_rs 0 is 0)) rs


----------------------------------------------------------------------
-- * Distributions in 'SupplyJointM'
----------------------------------------------------------------------

instance SupplyJointCtx supply r i =>
         Interp__normal (StandardHORepr (SupplyJointM supply) r i) where
  interp__normal = GExpr $ \ mu sigma dv ->
    do val <-
         case dv of
           VParam  -> supplyRealM
           VData x -> return $ embedVarData x
       updateJointProbM $ normalDensityGen mu sigma val
       return val

instance SupplyJointCtx supply r i =>
         Interp__uniform (StandardHORepr (SupplyJointM supply) r i) where
  interp__uniform = GExpr $ \ lb ub dv ->
    do val <-
         case dv of
           VParam  -> fromRealLbUb lb ub <$> supplyRealM
           VData x -> return $ embedVarData x
       updateJointProbM $ uniformDensityGen lb ub val
       return val

instance SupplyJointCtx supply r i =>
         Interp__categorical (StandardHORepr (SupplyJointM supply) r i) where
  interp__categorical = GExpr $ \ probs dv ->
    do i <-
         case dv of
           VParam -> supplyIntM
           VData i -> return $ embedVarData i
       let prob_exprs = toHaskellListF unGExpr probs
       updateJointProbM $ unGExpr $ prob_exprs !! fromIntegral i
       return i

--
-- * Matrix Distributions
--

-- FIXME HERE NOW: multivariate normal!
