{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Grappa.Interp.StandardHORepr where

import Control.Monad

import Language.Grappa.Distribution
import Language.Grappa.Interp
import Language.Grappa.GrappaInternals
import Language.Grappa.Frontend.DataSource

import qualified Data.Matrix as M
import qualified Numeric.Log as Log


----------------------------------------------------------------------
-- * The StandardHORepr Representation
----------------------------------------------------------------------

-- | The type tag for the standard higher-order representation, which is
-- parameterized by a monad and by the representation types for reals and ints
data StandardHORepr (m :: * -> *) (r :: *) (i :: *) :: *

-- | The type family for 'StandardHORepr' expressions
type family StandardHOReprF m r i a :: * where
  StandardHOReprF m r i (a -> b) =
    (StandardHOReprF m r i a -> StandardHOReprF m r i b)
  StandardHOReprF m r i (Dist' a) = (DistVar a -> m (StandardHOReprF m r i a))
  StandardHOReprF m r i (ADT adt) =
    adt (GExpr (StandardHORepr m r i)) (ADT adt)
  StandardHOReprF m r i Bool    = Bool
  StandardHOReprF m r i Int     = i
  StandardHOReprF m r i Prob    = Log.Log r
  StandardHOReprF m r i R       = r
  StandardHOReprF m r i RMatrix = M.Matrix r
  StandardHOReprF m r i a       = a

instance ValidExprRepr (StandardHORepr m r i) where
  type GExprRepr (StandardHORepr m r i) a = StandardHOReprF m r i a
  interp__'bottom = error "StandardHORepr: unexpected bottom!"
  interp__'injTuple !tup = GExpr tup
  interp__'projTuple (GExpr !tup) k = k tup
  interp__'app (GExpr !f) (GExpr x) = GExpr (f x)
  interp__'lam f = GExpr (unGExpr . f . GExpr)
  interp__'fix f = f (interp__'fix f)

instance StrongTupleRepr (StandardHORepr m r i) where
  interp__'strongProjTuple (GExpr tup) = tup

instance Monad m => ValidRepr (StandardHORepr m r i) where
  type GVExprRepr (StandardHORepr m r i) a = DistVar a
  type GStmtRepr (StandardHORepr m r i) a = m (StandardHOReprF m r i a)

  interp__'projTupleStmt (GExpr !tup) k = k tup

  interp__'vInjTuple !tup =
    GVExpr (VADT $ mapADT unGVExpr tup)
  interp__'vProjTuple (GVExpr (VADT !tup)) k =
    k $ mapADT GVExpr tup
  interp__'vProjTuple (GVExpr VParam) k =
    k $ mapADT (\ _ -> GVExpr VParam) typeListProxy

  interp__'vwild k = k (GVExpr VParam)
  interp__'vlift _ _ = error "FIXME HERE: interp__'vlift"

  interp__'return (GExpr !x) = GStmt (return x)
  interp__'let rhs body = body rhs
  interp__'sample (GExpr !d) (GVExpr !dv) k = GStmt $ do
    !x <- d dv
    unGStmt $ k (GExpr x)

  interp__'mkDist f = GExpr (\ dv -> unGStmt $ f $ GVExpr dv)

instance TraversableADT adt =>
         Interp__ADT__Expr (StandardHORepr m r i) adt where
  interp__'injADT adt = GExpr adt
  interp__'projADT (GExpr adt) k = k adt

instance (Monad m, TraversableADT adt) =>
         Interp__ADT (StandardHORepr m r i) adt where
  interp__'vInjADT adt =
    GVExpr (VADT $ mapADT unGVExpr adt)
  interp__'projADTStmt (GExpr adt) k = k adt

instance Interp__'source (StandardHORepr m Double Int) a where
  interp__'source src = GVExpr <$> interpSource src

instance EmbedRepr (StandardHORepr m Double i) R where
  embedRepr = GExpr

instance EmbedRepr (StandardHORepr m Double i) Prob where
  embedRepr = GExpr . fromProb

instance EmbedRepr (StandardHORepr m r Int) Int where
  embedRepr = GExpr

instance EmbedRepr (StandardHORepr m r Int) Bool where
  embedRepr = GExpr


----------------------------------------------------------------------
-- Boolean and comparison operations
----------------------------------------------------------------------

instance Interp__'ifThenElse (StandardHORepr m r i) where
  interp__'ifThenElse (GExpr c) t e = if c then t else e

instance Interp__not (StandardHORepr m r i) where
  interp__not = GExpr not

instance Interp__'amp'amp (StandardHORepr m r i) where
  interp__'amp'amp = GExpr (&&)

instance Interp__'bar'bar (StandardHORepr m r i) where
  interp__'bar'bar = GExpr (||)

instance (Eq a, Eq (StandardHOReprF m r i a)) =>
         Interp__'eq'eq (StandardHORepr m r i) a where
  interp__'eq'eq = GExpr (==)

instance (Ord a, Ord (StandardHOReprF m r i a)) =>
         Interp__'lt (StandardHORepr m r i) a where
  interp__'lt = GExpr (<)

instance (Ord a, Ord (StandardHOReprF m r i a)) =>
         Interp__'gt (StandardHORepr m r i) a where
  interp__'gt = GExpr (>)

instance (Ord a, Ord (StandardHOReprF m r i a)) =>
         Interp__'lt'eq (StandardHORepr m r i) a where
  interp__'lt'eq = GExpr (<=)

instance (Ord a, Ord (StandardHOReprF m r i a)) =>
         Interp__'gt'eq (StandardHORepr m r i) a where
  interp__'gt'eq = GExpr (>=)

instance (Ord a, Ord (StandardHOReprF m r i a)) =>
         Interp__min (StandardHORepr m r i) a where
  interp__min = GExpr min

instance (Ord a, Ord (StandardHOReprF m r i a)) =>
         Interp__max (StandardHORepr m r i) a where
  interp__max = GExpr max


----------------------------------------------------------------------
-- Numeric Operations
----------------------------------------------------------------------

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__'plus (StandardHORepr m r i) a where
  interp__'plus = GExpr (+)

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__'minus (StandardHORepr m r i) a where
  interp__'minus = GExpr (-)

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__'times (StandardHORepr m r i) a where
  interp__'times = GExpr (*)

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__negate (StandardHORepr m r i) a where
  interp__negate = GExpr negate

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__abs (StandardHORepr m r i) a where
  interp__abs = GExpr abs

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__signum (StandardHORepr m r i) a where
  interp__signum = GExpr signum

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__fromInteger (StandardHORepr m r i) a where
  interp__fromInteger = GExpr fromInteger

instance (Num a, Num (StandardHOReprF m r i a)) =>
         Interp__'integer (StandardHORepr m r i) a where
  interp__'integer n = GExpr (fromInteger n)

instance (Interp__'integer (StandardHORepr m r i) a,
          Eq (StandardHOReprF m r i a))
         => Interp__'eqInteger (StandardHORepr m r i) a where
  interp__'eqInteger (GExpr x) (GExpr y) = GExpr (x == y)


instance (Fractional a, Fractional (StandardHOReprF m r i a)) =>
         Interp__'div (StandardHORepr m r i) a where
  interp__'div = GExpr (/)

instance (Fractional a, Fractional (StandardHOReprF m r i a)) =>
         Interp__recip (StandardHORepr m r i) a where
  interp__recip = GExpr recip

instance (Fractional a, Fractional (StandardHOReprF m r i a)) =>
         Interp__fromRational (StandardHORepr m r i) a where
  interp__fromRational = GExpr fromRational

instance (Fractional a, Fractional (StandardHOReprF m r i a)) =>
         Interp__'rational (StandardHORepr m r i) a where
  interp__'rational n = GExpr (fromRational n)

instance (Interp__'rational (StandardHORepr m r i) a,
          Eq (StandardHOReprF m r i a))
         => Interp__'eqRational (StandardHORepr m r i) a where
  interp__'eqRational (GExpr x) (GExpr y) = GExpr (x == y)


instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__pi (StandardHORepr m r i) a where
  interp__pi = GExpr pi

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__exp (StandardHORepr m r i) a where
  interp__exp = GExpr exp

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__log (StandardHORepr m r i) a where
  interp__log = GExpr log

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__sqrt (StandardHORepr m r i) a where
  interp__sqrt = GExpr sqrt

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__'times'times (StandardHORepr m r i) a where
  interp__'times'times = GExpr (**)

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__logBase (StandardHORepr m r i) a where
  interp__logBase = GExpr logBase

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__sin (StandardHORepr m r i) a where
  interp__sin = GExpr sin

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__cos (StandardHORepr m r i) a where
  interp__cos = GExpr cos

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__tan (StandardHORepr m r i) a where
  interp__tan = GExpr tan

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__asin (StandardHORepr m r i) a where
  interp__asin = GExpr asin

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__acos (StandardHORepr m r i) a where
  interp__acos = GExpr acos

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__atan (StandardHORepr m r i) a where
  interp__atan = GExpr atan

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__sinh (StandardHORepr m r i) a where
  interp__sinh = GExpr sinh

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__cosh (StandardHORepr m r i) a where
  interp__cosh = GExpr cosh

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__tanh (StandardHORepr m r i) a where
  interp__tanh = GExpr tanh

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__asinh (StandardHORepr m r i) a where
  interp__asinh = GExpr asinh

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__acosh (StandardHORepr m r i) a where
  interp__acosh = GExpr acosh

instance (Floating a, Floating (StandardHOReprF m r i a)) =>
         Interp__atanh (StandardHORepr m r i) a where
  interp__atanh = GExpr atanh


----------------------------------------------------------------------
-- Probability expression operations
----------------------------------------------------------------------

instance (Ord r, Floating r) => Interp__realToProb (StandardHORepr m r i) where
  interp__realToProb = GExpr (Log.Exp . log . toNonNeg) where
    toNonNeg :: (Ord r, Floating r) => r -> r
    toNonNeg r = if r < 0 then 0 else r

instance Interp__logRealToProb (StandardHORepr m r i) where
  interp__logRealToProb = GExpr Log.Exp

instance Floating r => Interp__probToReal (StandardHORepr m r i) where
  interp__probToReal = GExpr (exp . Log.ln)

instance Interp__probToLogReal (StandardHORepr m r i) where
  interp__probToLogReal = GExpr Log.ln

instance HasGamma r => Interp__gammaProb (StandardHORepr m r i) where
  interp__gammaProb = GExpr logGamma


----------------------------------------------------------------------
-- Misc operations
----------------------------------------------------------------------

instance (Show a, Show (StandardHOReprF m r i a), i ~ Int) =>
         Interp__gtrace (StandardHORepr m r i) a b where
  interp__gtrace = GExpr gtrace

instance i ~ Int => Interp__gerror (StandardHORepr m r i) a where
  interp__gerror = GExpr gerror


----------------------------------------------------------------------
-- * Distributions Supported by All 'StandardHORepr' Representations
----------------------------------------------------------------------

instance Monad m => Interp__ctorDist__ListF (StandardHORepr m r i) where
  interp__ctorDist__Nil = GExpr $ \ mkNil dv ->
    do _ <- case dv of
              VParam      -> mkNil VParam
              VADT Nil    -> mkNil (VADT Tuple0)
              VADT Cons{} -> error "Unexpected Cons"
       return Nil

  interp__ctorDist__Cons = GExpr $ \ mkCons dv ->
    do Tuple2 hd tl <-
         case dv of
           VParam              -> mkCons (VADT (Tuple2 VParam VParam))
           VADT Nil            -> error "Unexpected Nil"
           VADT (Cons hdv tlv) -> mkCons (VADT (Tuple2 hdv tlv))
       return (Cons hd tl)


-- If a repr can do a categorical, it can do an ADT distribution on lists
instance (Monad m, Num i, Eq i, Show i,
          Interp__categorical (StandardHORepr m r i)) =>
         Interp__adtDist__ListF (StandardHORepr m r i) where
  interp__adtDist__ListF =
    GExpr $ \ probNil mkNil probCons mkCons dvList ->
    let
      -- Build a categorical distribution for the constructor, where 0 -> Nil
      -- and 1 -> Cons
      ctor_dist :: DistVar Int -> m (StandardHOReprF m r i Int)
      ctor_dist =
        unGExpr (interp__categorical
                 :: GExpr (StandardHORepr m r i) (GList Prob -> Dist' Int)) $
        fromHaskellListF GExpr [GExpr probNil, GExpr probCons]
      -- Helper wrapper around mkNil
      mkNilH = mkNil (VADT Tuple0)
      -- Helper wrapper around mkCons, that takes vars for the head and tail
      mkConsH hdv tlv =
        do Tuple2 hd tl <- mkCons (VADT (Tuple2 hdv tlv))
           return (Cons hd tl) in
    case dvList of
      VParam ->
        do ctor_choice <- ctor_dist VParam
           case ctor_choice of
             0 -> void mkNilH >> return Nil
             1 -> mkConsH VParam VParam
             _ -> error ("ListF: Invalid constructor choice: "
                         ++ show ctor_choice)

      VADT Nil ->
        void (ctor_dist $ VData 0) >> void mkNilH >> return Nil

      VADT (Cons hdv tlv) ->
        void (ctor_dist $ VData 1) >> mkConsH hdv tlv


--
-- * Matrix Operations
--

-- FIXME HERE NOW: matrix operations!
