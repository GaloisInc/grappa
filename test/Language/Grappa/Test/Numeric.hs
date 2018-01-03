{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Grappa.Test.Numeric where

import qualified Numeric.AD.Mode as AD
import qualified Numeric.Log as Log
import Test.Hspec
import Test.QuickCheck as Qc
import Test.QuickCheck.Property ((===))
import Test.QuickCheck.Property as Qc

import Debug.Trace

import Language.Grappa.Distribution
import Language.Grappa.Interp.AD

tests :: Spec
tests = do
  describe "ADR" $ do
    it "should preserve + from R" $
      numericBinOp (+) Qc.arbitrary doubleToADR
    it "should preserve - from R" $
      numericBinOp (-) Qc.arbitrary doubleToADR
    it "should preserve * from R" $
      numericBinOp (*) Qc.arbitrary doubleToADR

    it "should preserve negate from R" $
      numericUnOp negate Qc.arbitrary doubleToADR
    it "should preserve abs from R" $
      numericUnOp abs Qc.arbitrary doubleToADR
    it "should preserve signum from R" $
      numericUnOp signum Qc.arbitrary doubleToADR

    it "should preserve == from R" $
      numericCmpOp (==) Qc.arbitrary doubleToADR
    it "should preserve /= from R" $
      numericCmpOp (/=) Qc.arbitrary doubleToADR
    it "should preserve < from R" $
      numericCmpOp (<) Qc.arbitrary doubleToADR
    it "should preserve > from R" $
      numericCmpOp (>) Qc.arbitrary doubleToADR
    it "should preserve <= from R" $
      numericCmpOp (<=) Qc.arbitrary doubleToADR
    it "should preserve >= from R" $
      numericCmpOp (>=) Qc.arbitrary doubleToADR

  describe "ADProb" $ do
    it "should preserve + from Prob" $
      numericBinOp (+) arbProb probToADProb
    it "should preserve - from Prob" $
      numericBinOp (-) arbProb probToADProb
    it "should preserve * from Prob" $
      numericBinOp (*) arbProb probToADProb

    it "should preserve negate from Prob" $
      numericUnOp negate arbProb probToADProb
    it "should preserve abs from Prob" $
      numericUnOp abs arbProb probToADProb
    it "should preserve signum from Prob" $
      numericUnOp signum arbProb probToADProb

    it "should preserve == from Prob" $
      numericCmpOp (==) arbProb probToADProb
    it "should preserve /= from Prob" $
      numericCmpOp (/=) arbProb probToADProb
    it "should preserve < from Prob" $
      numericCmpOp (<) arbProb probToADProb
    it "should preserve > from Prob" $
      numericCmpOp (>) arbProb probToADProb
    it "should preserve <= from Prob" $
      numericCmpOp (<=) arbProb probToADProb
    it "should preserve >= from Prob" $
      numericCmpOp (>=) arbProb probToADProb

arbProb :: Qc.Gen Prob
arbProb = Prob . Log.Exp <$> Qc.arbitrary

probToADProb :: Prob -> ADProb
probToADProb (Prob (Log.Exp n)) = Log.Exp (AD.auto n)

doubleToADR :: Double -> ADR
doubleToADR = AD.auto

arbADR :: Qc.Gen ADR
arbADR = AD.auto <$> Qc.arbitrary

numericBinOp :: (Show n, Show m, Num n, Num m, Eq m) =>
                (forall a. Num a => a -> a -> a) ->
                Qc.Gen n -> (n -> m) -> Qc.Property
numericBinOp op gen inj =
  Qc.forAll gen $ \n ->
  Qc.forAll gen $ \m ->
  let wrap True = True
      wrap False = trace msg False
      msg = (show (inj (n `op` m)))
  in wrap (inj (n `op` m) == inj n `op` inj m)

numericUnOp :: (Show n, Show m, Num n, Num m, Eq m) =>
                (forall a. Num a => a -> a) ->
                Qc.Gen n -> (n -> m) -> Qc.Property
numericUnOp op gen inj =
  Qc.forAll gen $ \n ->
  inj (op n) == op (inj n)

numericCmpOp :: (Show n, Show m, Ord n, Ord m) =>
                (forall a. Ord a => a -> a -> Bool) ->
                Qc.Gen n -> (n -> m) -> Qc.Property
numericCmpOp op gen inj =
  Qc.forAll gen $ \n ->
  Qc.forAll gen $ \m ->
  n `op` m == inj n `op` inj m
