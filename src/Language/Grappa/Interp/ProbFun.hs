{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.Grappa.Interp.ProbFun where

import Data.Vector (Vector)
import Data.Functor.Compose

import Language.Grappa.Distribution
import Language.Grappa.Interp
import Language.Grappa.GrappaInternals
import Language.Grappa.Interp.PVIE
import GHC.Exts (IsList(..))

-- | Type tag for the representation that views @'Dist' a@ as a function from
-- @a@ to 'Prob'
data ProbFunRepr

type family ProbFunReprF a where
  ProbFunReprF (a -> b) = (ProbFunReprF a -> ProbFunReprF b)
  ProbFunReprF (Dist a) = ProbFunReprF a -> Prob
  ProbFunReprF (ADT adt) = adt (GExpr ProbFunRepr) (ADT adt)
  ProbFunReprF (Vector a) = Vector (ProbFunReprF a)
  ProbFunReprF (VIDist a) = (VIDistFamExpr (ProbFunReprF a))
  ProbFunReprF VISize = VIDim
  ProbFunReprF a = a

instance ValidExprRepr ProbFunRepr where
  type GExprRepr ProbFunRepr a = ProbFunReprF a
  interp__'bottom = error "ProbFunRepr: unexpected bottom!"
  interp__'injTuple tup = GExpr tup
  interp__'projTuple (GExpr tup) k = k tup
  interp__'app (GExpr f) (GExpr x) = GExpr (f x)
  interp__'lam f = GExpr (unGExpr . f . GExpr)
  interp__'fix f = f (interp__'fix f)

instance ValidRepr ProbFunRepr where
  type GVExprRepr ProbFunRepr a = ProbFunReprF a
  type GStmtRepr ProbFunRepr a = Prob

  interp__'projTupleStmt (GExpr tup) k = k tup

  interp__'vInjTuple tup = GVExpr $ mapADT (GExpr . unGVExpr) tup
  interp__'vProjTuple (GVExpr ve) k = k $ mapADT (GVExpr . unGExpr) ve

  interp__'vwild _ = error "ProbFunRepr: wildcard variables not allowed!"
  interp__'vlift (GExpr e) k = k (GVExpr e)

  interp__'return (GExpr _) = GStmt 1
  interp__'let rhs body = body rhs
  interp__'sample (GExpr d) (GVExpr v) k =
    -- FIXME: evaluate these two sides in parallel!
    GStmt $ d v + unGStmt (k $ GExpr v)

  interp__'mkDist f = GExpr (\ dv -> unGStmt $ f $ GVExpr dv)

instance TraversableADT adt =>
         Interp__ADT__Expr ProbFunRepr adt where
  interp__'injADT adt = GExpr adt
  interp__'projADT (GExpr adt) k = k adt
  interp__'projMatchADT (GExpr adt) _ matcher k_succ k_fail =
    if applyCtorMatcher matcher adt then k_succ adt else k_fail

instance TraversableADT adt => Interp__ADT ProbFunRepr adt where
  interp__'vInjADT adt = GVExpr (mapADT (GExpr . unGVExpr) adt)
  interp__'vProjMatchADT (GVExpr adt) _ matcher k_succ k_fail =
    if applyCtorMatcher matcher adt then
      k_succ (mapADT (GVExpr . unGExpr) adt)
    else k_fail

instance EmbedRepr ProbFunRepr Bool where
  embedRepr = GExpr
instance EmbedRepr ProbFunRepr Int where
  embedRepr = GExpr
instance EmbedRepr ProbFunRepr R where
  embedRepr = GExpr
instance EmbedRepr ProbFunRepr Prob where
  embedRepr = GExpr

instance IsList (ListF a (GExpr ProbFunRepr) (ADT (ListF a))) where
  type Item (ListF a (GExpr ProbFunRepr) (ADT (ListF a))) = ProbFunReprF a
  fromList [] = Nil
  fromList (x:xs) = (Cons (GExpr x) (GExpr (fromList xs)))
  toList Nil = []
  toList (Cons (GExpr x) (GExpr xs)) = x : toList xs


----------------------------------------------------------------------
-- Boolean and comparison operations
----------------------------------------------------------------------

instance Interp__'ifThenElse ProbFunRepr where
  interp__'ifThenElse (GExpr c) t e = if c then t else e

instance Interp__'vmatchSwitch ProbFunRepr where
  interp__'vmatchSwitch (GExpr i) stmts = stmts !! i

instance Interp__not ProbFunRepr where
  interp__not = GExpr not

instance Interp__'amp'amp ProbFunRepr where
  interp__'amp'amp = GExpr (&&)

instance Interp__'bar'bar ProbFunRepr where
  interp__'bar'bar = GExpr (||)

instance (Eq a, Eq (ProbFunReprF a)) =>
         Interp__'eq'eq ProbFunRepr a where
  interp__'eq'eq = GExpr (==)

instance (Ord a, Ord (ProbFunReprF a)) =>
         Interp__'lt ProbFunRepr a where
  interp__'lt = GExpr (<)

instance (Ord a, Ord (ProbFunReprF a)) =>
         Interp__'gt ProbFunRepr a where
  interp__'gt = GExpr (>)

instance (Ord a, Ord (ProbFunReprF a)) =>
         Interp__'lt'eq ProbFunRepr a where
  interp__'lt'eq = GExpr (<=)

instance (Ord a, Ord (ProbFunReprF a)) =>
         Interp__'gt'eq ProbFunRepr a where
  interp__'gt'eq = GExpr (>=)

instance (Ord a, Ord (ProbFunReprF a)) =>
         Interp__min ProbFunRepr a where
  interp__min = GExpr min

instance (Ord a, Ord (ProbFunReprF a)) =>
         Interp__max ProbFunRepr a where
  interp__max = GExpr max


----------------------------------------------------------------------
-- Numeric Operations
----------------------------------------------------------------------

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__'plus ProbFunRepr a where
  interp__'plus = GExpr (+)

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__'minus ProbFunRepr a where
  interp__'minus = GExpr (-)

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__'times ProbFunRepr a where
  interp__'times = GExpr (*)

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__negate ProbFunRepr a where
  interp__negate = GExpr negate

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__abs ProbFunRepr a where
  interp__abs = GExpr abs

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__signum ProbFunRepr a where
  interp__signum = GExpr signum

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__fromInteger ProbFunRepr a where
  interp__fromInteger = GExpr fromInteger

instance (Num a, Num (ProbFunReprF a)) =>
         Interp__'integer ProbFunRepr a where
  interp__'integer n = GExpr (fromInteger n)

instance (Interp__'integer ProbFunRepr a,
          Eq (ProbFunReprF a))
         => Interp__'eqInteger ProbFunRepr a where
  interp__'eqInteger (GExpr x) (GExpr y) = GExpr (x == y)


instance (Fractional a, Fractional (ProbFunReprF a)) =>
         Interp__'div ProbFunRepr a where
  interp__'div = GExpr (/)

instance (Fractional a, Fractional (ProbFunReprF a)) =>
         Interp__recip ProbFunRepr a where
  interp__recip = GExpr recip

instance (Fractional a, Fractional (ProbFunReprF a)) =>
         Interp__fromRational ProbFunRepr a where
  interp__fromRational = GExpr fromRational

instance (Fractional a, Fractional (ProbFunReprF a)) =>
         Interp__'rational ProbFunRepr a where
  interp__'rational n = GExpr (fromRational n)

instance (Interp__'rational ProbFunRepr a,
          Eq (ProbFunReprF a))
         => Interp__'eqRational ProbFunRepr a where
  interp__'eqRational (GExpr x) (GExpr y) = GExpr (x == y)


instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__pi ProbFunRepr a where
  interp__pi = GExpr pi

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__exp ProbFunRepr a where
  interp__exp = GExpr exp

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__log ProbFunRepr a where
  interp__log = GExpr log

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__sqrt ProbFunRepr a where
  interp__sqrt = GExpr sqrt

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__'times'times ProbFunRepr a where
  interp__'times'times = GExpr (**)

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__logBase ProbFunRepr a where
  interp__logBase = GExpr logBase

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__sin ProbFunRepr a where
  interp__sin = GExpr sin

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__cos ProbFunRepr a where
  interp__cos = GExpr cos

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__tan ProbFunRepr a where
  interp__tan = GExpr tan

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__asin ProbFunRepr a where
  interp__asin = GExpr asin

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__acos ProbFunRepr a where
  interp__acos = GExpr acos

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__atan ProbFunRepr a where
  interp__atan = GExpr atan

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__sinh ProbFunRepr a where
  interp__sinh = GExpr sinh

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__cosh ProbFunRepr a where
  interp__cosh = GExpr cosh

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__tanh ProbFunRepr a where
  interp__tanh = GExpr tanh

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__asinh ProbFunRepr a where
  interp__asinh = GExpr asinh

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__acosh ProbFunRepr a where
  interp__acosh = GExpr acosh

instance (Floating a, Floating (ProbFunReprF a)) =>
         Interp__atanh ProbFunRepr a where
  interp__atanh = GExpr atanh


----------------------------------------------------------------------
-- Probability expression operations
----------------------------------------------------------------------

instance Interp__realToProb ProbFunRepr where
  interp__realToProb = GExpr $ \x ->
    if x < 0 then 0 else rToProb x

instance Interp__logRealToProb ProbFunRepr where
  interp__logRealToProb = GExpr logRToProb

instance Interp__probToReal ProbFunRepr where
  interp__probToReal = GExpr probToR

instance Interp__probToLogReal ProbFunRepr where
  interp__probToLogReal = GExpr probToLogR

instance Interp__gammaProb ProbFunRepr where
  interp__gammaProb = GExpr (Prob . logGamma)


----------------------------------------------------------------------
-- Misc operations
----------------------------------------------------------------------

instance (Show a, Show (ProbFunReprF a)) =>
         Interp__gtrace ProbFunRepr a b where
  interp__gtrace = GExpr gtrace

instance Interp__gerror ProbFunRepr a where
  interp__gerror = GExpr gerror


----------------------------------------------------------------------
-- Interpreting Distributions
----------------------------------------------------------------------

instance Interp__normal ProbFunRepr where
  interp__normal = GExpr normalDensity

instance Interp__uniform ProbFunRepr where
  interp__uniform = GExpr uniformDensity

instance Interp__gamma ProbFunRepr where
  interp__gamma = GExpr $ \k theta x -> Prob $ gammaDensity k theta x

instance Interp__beta ProbFunRepr where
  interp__beta = GExpr $ \alpha beta x -> Prob $ betaDensity alpha beta x

instance Interp__dirichlet ProbFunRepr where
  interp__dirichlet = GExpr $ \alphas xs ->
    Prob $ dirichletDensity (toList alphas) (toList xs)

instance Interp__categorical ProbFunRepr where
  interp__categorical = GExpr $ \probs x ->
    if x >= length (toList probs) then 0 else
      (toList probs) !! x

instance Interp__ctorDist__ListF ProbFunRepr where
  interp__ctorDist__Nil = GExpr $ \d xs ->
    case xs of
      Nil -> d Tuple0
      _ -> error "Unexpected Cons!"
  interp__ctorDist__Cons = GExpr $ \d xs ->
    case xs of
      Cons x xs' -> d (Tuple2 x xs')
      _ -> error "Unexpected Nil!"

instance Interp__adtDist__ListF ProbFunRepr where
  interp__adtDist__ListF = GExpr $ \probNil dNil probCons dCons xs ->
    case xs of
      Nil -> probNil * dNil Tuple0
      Cons x xs' -> probCons * dCons (Tuple2 x xs')


----------------------------------------------------------------------
-- Interpreting VI Distribution Families
----------------------------------------------------------------------

instance Interp__withVISize ProbFunRepr where
  interp__withVISize = GExpr $ \f -> bindVIDimFamExpr f

instance Interp__viNormal ProbFunRepr where
  interp__viNormal = GExpr normalVIFamExpr

instance Interp__viUniform ProbFunRepr where
  interp__viUniform = GExpr uniformVIFamExpr

instance Interp__viCategorical ProbFunRepr where
  interp__viCategorical = GExpr categoricalVIFamExpr

instance Interp__viTuple0 ProbFunRepr where
  interp__viTuple0 = GExpr $ tupleVIFamExpr Tuple0

instance Interp__viTuple1 ProbFunRepr a where
  interp__viTuple1 = GExpr $ \da ->
    tupleVIFamExpr (Tuple1 $ Compose $ xformVIDistFamExpr GExpr unGExpr da)

instance Interp__viTuple2 ProbFunRepr a b where
  interp__viTuple2 = GExpr $ \da db ->
    tupleVIFamExpr (Tuple2
                    (Compose $ xformVIDistFamExpr GExpr unGExpr da)
                    (Compose $ xformVIDistFamExpr GExpr unGExpr db))

instance Interp__viTuple3 ProbFunRepr a b c where
  interp__viTuple3 = GExpr $ \da db dc ->
    tupleVIFamExpr (Tuple3
                    (Compose $ xformVIDistFamExpr GExpr unGExpr da)
                    (Compose $ xformVIDistFamExpr GExpr unGExpr db)
                    (Compose $ xformVIDistFamExpr GExpr unGExpr dc))

instance Interp__viTuple4 ProbFunRepr a b c d where
  interp__viTuple4 = GExpr $ \da db dc dd ->
    tupleVIFamExpr (Tuple4
                    (Compose $ xformVIDistFamExpr GExpr unGExpr da)
                    (Compose $ xformVIDistFamExpr GExpr unGExpr db)
                    (Compose $ xformVIDistFamExpr GExpr unGExpr dc)
                    (Compose $ xformVIDistFamExpr GExpr unGExpr dd))
