{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Grappa.Interp.InitSupply (
  InitSupplyM(..), runInitSupplyM, InitSupplyRepr, initSupply
  ) where

import Data.IORef
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer

import Language.Grappa.Distribution
import Language.Grappa.Interp
import Language.Grappa.Interp.Supply
import Language.Grappa.GrappaInternals
import Language.Grappa.Rand.MWCRandM
import Language.Grappa.Interp.StandardHORepr

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

-- import qualified Data.Matrix as M
-- import qualified Numeric.Log as Log


----------------------------------------------------------------------
-- * The Monad for Initializing / Completing Supplies
----------------------------------------------------------------------

-- | The monad for initializing / completing supplies
newtype InitSupplyM supply a =
  InitSupplyM { unInitSupplyM ::
                  ReaderT (IORef supply) (WriterT (SupplyUpdate supply) MWCRandM) a
              } deriving (Functor,Applicative,Monad)

genReal :: Supply supply => MWCRandM (SupplyReal supply) ->
           InitSupplyM supply (SupplyReal supply)
genReal gen = InitSupplyM $
  do supply_ref <- ask
     supply <- liftIO $ readIORef supply_ref
     (r, supply') <- lift $ lift $ supplyRealWithDefault supply gen
     liftIO $ writeIORef supply_ref supply'
     tell [Right r]
     return r

genInt :: Supply supply => MWCRandM (SupplyInt supply) ->
          InitSupplyM supply (SupplyInt supply)
genInt gen = InitSupplyM $
  do supply_ref <- ask
     supply <- liftIO $ readIORef supply_ref
     (i, supply') <- lift $ lift $ supplyIntWithDefault supply gen
     liftIO $ writeIORef supply_ref supply'
     tell [Left i]
     return i


----------------------------------------------------------------------
-- * Run Methods for 'SupplyJointM'
----------------------------------------------------------------------

-- | Run an 'InitSupplyM' computation to initialize / complete a supply
runInitSupplyM :: Supply supply => InitSupplyM supply a -> supply ->
                  MWCRandM (a, supply)
runInitSupplyM (InitSupplyM m) supply =
  do supply_ref <- liftIO $ newIORef supply
     (a, vals) <- runWriterT (runReaderT m supply_ref)
     return (a, updateSupply supply vals)

-- | Shorthand for a 'StandardHORepr' using 'InitSupplyM'
type InitSupplyRepr supply =
  StandardHORepr (InitSupplyM supply) (SupplyReal supply) (SupplyInt supply)

-- | Initialize / complete a supply
initSupply :: Supply supply => GStmt (InitSupplyRepr supply) a -> supply ->
              MWCRandM supply
initSupply stmt supply =
  snd <$> runInitSupplyM (unGStmt stmt) supply


----------------------------------------------------------------------
-- * Combinators for Real-Valued Distributions
----------------------------------------------------------------------

-- | The typeclass context needed for distributions using 'InitSupplyRepr'
type DistCtx supply =
  (Supply supply, SupplyReal supply ~ Double, SupplyInt supply ~ Int)

-- | An 'InitSupplyRepr' with a 'Supply' that uses 'Double' and 'Int'
type InitSupplyReprDI supply =
  StandardHORepr (InitSupplyM supply) Double Int

instance DistCtx supply => Interp__normal (InitSupplyReprDI supply) where
  interp__normal = GExpr $ \ mu sigma dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (genReal $ random $ MWC.normal mu sigma)

instance DistCtx supply => Interp__uniform (InitSupplyReprDI supply) where
  interp__uniform = GExpr $ \ lb ub dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (fromRealLbUb lb ub <$>
     genReal (toRealLbUb lb ub <$> random (MWC.uniformR (lb, ub))))

instance DistCtx supply => Interp__categorical (InitSupplyReprDI supply) where
  interp__categorical = GExpr $ \ probs dv ->
    matchHOReprAtomicDistVar dv (return . unGExpr)
    (genInt $ mwcCategorical $ map (Prob . unGExpr) $
     toHaskellListF unGExpr probs)


----------------------------------------------------------------------
-- * Combinators for List Distributions
----------------------------------------------------------------------

-- FIXME: remove this? Should be taken care of by the StandardHORepr instance
{-
instance DistCtx supply =>
         Interp__adtDist__ListF (InitSupplyReprDI supply) where
  interp__adtDist__ListF =
    GExpr $ \ probNil mkNil probCons mkCons dvList ->
    do let genNil =
             do _ <- mkNil (VADT Tuple0)
                return Nil

           genCons hdv tlv =
             do Tuple2 hd tl <- mkCons (VADT (Tuple2 hdv tlv))
                return (Cons hd tl)
       matchHOReprADTDistVar
       case dvList of
         VParam ->
           do choice <- genInt 2
                (random (MWC.bernoulli $ Log.ln $
                         probCons / (probNil + probCons)) >>= \is1 ->
                  return (if is1 then 1 else 0))
              case choice of

                -- Make a Nil
                0 -> genNil

                -- Make a Cons
                1 -> genCons VParam VParam

                -- Invalid choice for this hard-coded use of the categorical
                -- distribution
                _ -> error ("ListF: Invalid constructor choice: " ++ show choice)

         VADT Nil -> genNil
         VADT (Cons hdv tlv) -> genCons hdv tlv
-}
