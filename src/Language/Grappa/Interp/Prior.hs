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

import Data.Maybe

import qualified Data.Vector as V

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

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

instance Interp__delta PriorRepr Int where
  interp__delta = GExpr $ \i dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (PriorM $ return i)

instance Interp__normal PriorRepr where
  interp__normal = GExpr $ \ mu sigma dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (PriorM $ mwcNormal mu sigma)

instance Interp__uniform PriorRepr where
  interp__uniform = GExpr $ \ lb ub dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (PriorM $ random $ MWC.uniformR (lb, ub))

instance Interp__exponential PriorRepr where
  interp__exponential = GExpr $ \ rate dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (PriorM $ mwcExponential rate)

instance Interp__gamma PriorRepr where
  interp__gamma = GExpr $ \k theta dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (PriorM $ random $ MWC.gamma k theta)

instance Interp__dirichlet PriorRepr where
  interp__dirichlet = GExpr $ \alphas_gexpr dv ->
    let (dvs, end_missing) = matchHOReprListDistVar dv
        maybe_vs =
          map (\dv' -> matchHOReprAtomicDistVar dv' (Just . unGExpr) Nothing)
          dvs
        alphas = map unGExpr $ toHaskellListF unGExpr alphas_gexpr in
    if all isNothing maybe_vs then
      -- If all values are missing, sample from the dirichlet distribution. This
      -- allows the end of the list to be missing too, in which case this sample
      -- will supply all its values
      if length alphas == length maybe_vs ||
         (length alphas >= length maybe_vs && end_missing) then
        fromHaskellListF GExpr <$> map GExpr <$> PriorM (mwcDirichlet alphas)
      else error "Dirichlet distribution: wrong number of values"
    else
      if all isJust maybe_vs then
        -- If all values are present, just return them
        if length alphas == length maybe_vs then
          return $ fromHaskellListF GExpr $ map (GExpr . fromJust) maybe_vs
        else
          error "Dirichlet distribution: wrong number of values"
      else
        error "Dirichlet distribution: cannot (yet) sample when some elements are present"

instance Interp__categorical PriorRepr where
  interp__categorical = GExpr $ \ probs dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (let ws =
           V.fromList $ map (Log.ln . unGExpr) $
           toHaskellListF unGExpr probs in
     PriorM $ random $ MWC.logCategorical ws)
