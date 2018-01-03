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
{-# LANGUAGE ViewPatterns #-}

module Language.Grappa.Interp.Prior (
  PriorRepr, PriorReprF, PriorM, samplePrior
  ) where

import qualified Data.Vector as V

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

import Language.Grappa.Distribution
import Language.Grappa.Interp
import Language.Grappa.GrappaInternals
import Language.Grappa.Rand.MWCRandM
import Language.Grappa.Interp.StandardHORepr

import qualified Numeric.Log as Log


----------------------------------------------------------------------
-- * The PriorM Monad, for Sampling from the Prior
----------------------------------------------------------------------

-- | Simple type wrapper around 'MWCRandM'
newtype PriorM a = PriorM { runPriorM :: MWCRandM a }
                 deriving (Functor, Applicative, Monad)

-- | Shorthand for a 'StandardHORepr' using 'PriorM'
type PriorRepr = StandardHORepr PriorM Double Int

-- | Shorthand for a 'StandardHOReprF' using 'PriorM'
type PriorReprF a = StandardHOReprF PriorM Double Int a

-- | Sample from the prior of a 'GStmt' using the 'PriorRepr' representation
samplePrior :: GStmt PriorRepr a -> MWCRandM (PriorReprF a)
samplePrior stmt = runPriorM $ unGStmt stmt


----------------------------------------------------------------------
-- * Distributions
----------------------------------------------------------------------

instance Interp__normal (StandardHORepr PriorM Double i) where
  interp__normal = GExpr $ \ mu sigma dv ->
    case dv of
      VParam  ->
        PriorM $
        -- FIXME HERE: the following line causes a GHC panic!
        -- random $ MWC.normal mu sigma
        distSample (Normal mu sigma)
      VData x -> return x

instance Interp__uniform (StandardHORepr PriorM Double i) where
  interp__uniform = GExpr $ \ lb ub dv ->
    case dv of
      VParam  -> PriorM $ random $ MWC.uniformR (lb, ub)
      VData x -> return x

instance Interp__gamma (StandardHORepr PriorM Double i) where
  interp__gamma = GExpr $ \k theta dv ->
    case dv of
      VParam  -> PriorM $ random $ MWC.gamma k theta
      VData x -> return x

instance Interp__dirichlet (StandardHORepr PriorM Double i) where
  interp__dirichlet = GExpr $ \alphas dv ->
    fromHaskellListF GExpr <$> map GExpr <$>
    helper (map unGExpr $ toHaskellListF unGExpr alphas) dv
    where
      helper :: [Double] -> DistVar (GList Double) -> PriorM [Double]
      helper alphas VParam = sample_vals alphas
      helper alphas (getDatas -> Just xs) =
        if length alphas == length xs then return xs else
          error $ "Dirichlet distribution: wrong number of input data points!"
      helper alphas _ = sample_vals alphas

      sample_vals :: [Double] -> PriorM [Double]
      sample_vals alphas = PriorM (random $ MWC.dirichlet alphas)

      getDatas :: DistVar (GList R) -> Maybe [Double]
      getDatas VParam = Nothing
      getDatas (VADT Nil) = Just []
      getDatas (VADT (Cons VParam _)) = Nothing
      getDatas (VADT (Cons (VData x) rest)) = (x :) <$> getDatas rest

instance Interp__categorical (StandardHORepr PriorM Double Int) where
  interp__categorical = GExpr $ \ probs dv ->
    case dv of
      VParam ->
        let ws =
              V.fromList $ map (Log.ln . unGExpr) $
              toHaskellListF unGExpr probs in
        PriorM $ random $ MWC.logCategorical ws
      VData i -> return i
