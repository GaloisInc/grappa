{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Grappa.Interp.MonoidRepr where

import Language.Grappa.GrappaInternals
import Language.Grappa.Interp


--
-- * The Monoid Representation
--

-- | The monoid representation computes a value for each program term, like most
-- normal dataflow analyses. The type of the output of the dataflow should
-- satisfy 'Monoid', since there must be a least element and a way to combine
-- values, and should also allow testing for equality: these are reflected in
-- the typeclass constraints for 'MonoidRepr' to be valid.
data MonoidRepr w

instance (Monoid w, Eq w) => ValidExprRepr (MonoidRepr w) where
  type GExprRepr (MonoidRepr w) a = w
  interp__'bottom = GExpr mempty
  interp__'injTuple tup = GExpr $ foldrADT unGExpr mappend mempty tup
  interp__'projTuple (GExpr w) projF =
    projF (mapADT (const $ GExpr w) typeListProxy)
  interp__'app (GExpr w1) (GExpr w2) = GExpr $ mappend w1 w2
  interp__'lam f =
    -- Take the least output value of the function, which, by the assumption of
    -- monotonicitiy, should be f bottom
    GExpr $ unGExpr $ f $ GExpr mempty
  interp__'fix f =
    -- Take the least fixed-point, starting at bottom = mempty
    helper (GExpr mempty) where
    helper w = if unGExpr (f w) == unGExpr w then w else helper (f w)

instance (Monoid w, Eq w) => StrongTupleRepr (MonoidRepr w) where
  interp__'strongProjTuple (GExpr w) = buildTuple (GExpr w)

instance (Monoid w, Eq w, TraversableADT adt, ReifyCtorsADT adt) =>
         Interp__ADT__Expr (MonoidRepr w) adt where
  interp__'injADT adt =
    GExpr $ foldrADT unGExpr mappend mempty adt
  interp__'projADT (GExpr w1) projF =
    GExpr $ mconcat $ map (unGExpr . projF . mapADT (\_ -> GExpr w1)) $
    reifyCtorsADT
  interp__'projMatchADT (GExpr w1) ctor_proxy _ k_succ (GExpr w_fail) =
    GExpr $ mappend w1 $ mappend w_fail $
    unGExpr $ k_succ $ mapADT (\_ -> interp__'bottom) ctor_proxy


----------------------------------------------------------------------
-- Interpreting the Operations
----------------------------------------------------------------------

-- NOTE: we interpret all the operations as bottom, so the only way to get a
-- non-bottom value in the monoid is from someone using MonoidRepr in a larger
-- context...

--
-- Boolean Expressions
--

instance (Monoid w, Eq w) => Interp__'ifThenElse (MonoidRepr w) where
  interp__'ifThenElse (GExpr w1) (GExpr w2) (GExpr w3) =
    GExpr $ mconcat [w1, w2, w3]

instance (Monoid w, Eq w) => Interp__not (MonoidRepr w) where
  interp__not = interp__'bottom

instance (Monoid w, Eq w) => Interp__'amp'amp (MonoidRepr w) where
  interp__'amp'amp = interp__'bottom

instance (Monoid w, Eq w) => Interp__'bar'bar (MonoidRepr w) where
  interp__'bar'bar = interp__'bottom


--
-- Comparison expressions
--

instance (Eq a, Monoid w, Eq w) => Interp__'eq'eq (MonoidRepr w) a where
  interp__'eq'eq = interp__'bottom

instance (Ord a, Monoid w, Eq w) => Interp__'lt (MonoidRepr w) a where
  interp__'lt = interp__'bottom

instance (Ord a, Monoid w, Eq w) => Interp__'gt (MonoidRepr w) a where
  interp__'gt = interp__'bottom

instance (Ord a, Monoid w, Eq w) => Interp__'lt'eq (MonoidRepr w) a where
  interp__'lt'eq = interp__'bottom

instance (Ord a, Monoid w, Eq w) => Interp__'gt'eq (MonoidRepr w) a where
  interp__'gt'eq = interp__'bottom

instance (Ord a, Monoid w, Eq w) => Interp__min (MonoidRepr w) a where
  interp__min = interp__'bottom

instance (Ord a, Monoid w, Eq w) => Interp__max (MonoidRepr w) a where
  interp__max = interp__'bottom


--
-- Numeric expressions
--

instance (Num a, Monoid w, Eq w) => Interp__'plus (MonoidRepr w) a where
  interp__'plus = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__'minus (MonoidRepr w) a where
  interp__'minus = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__'times (MonoidRepr w) a where
  interp__'times = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__negate (MonoidRepr w) a where
  interp__negate = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__abs (MonoidRepr w) a where
  interp__abs = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__signum (MonoidRepr w) a where
  interp__signum = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__fromInteger (MonoidRepr w) a where
  interp__fromInteger = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__'integer (MonoidRepr w) a where
  interp__'integer _ = interp__'bottom

instance (Num a, Monoid w, Eq w) => Interp__'eqInteger (MonoidRepr w) a where
  interp__'eqInteger (GExpr w1) (GExpr w2) = GExpr $ mappend w1 w2


instance (Fractional a, Monoid w, Eq w) => Interp__'div (MonoidRepr w) a where
  interp__'div = interp__'bottom

instance (Fractional a, Monoid w, Eq w) => Interp__recip (MonoidRepr w) a where
  interp__recip = interp__'bottom

instance (Fractional a, Monoid w, Eq w) =>
         Interp__fromRational (MonoidRepr w) a where
  interp__fromRational = interp__'bottom

instance (Fractional a, Monoid w, Eq w) =>
         Interp__'rational (MonoidRepr w) a where
  interp__'rational _ = interp__'bottom

instance (Fractional a, Monoid w, Eq w) =>
         Interp__'eqRational (MonoidRepr w) a where
  interp__'eqRational (GExpr w1) (GExpr w2) = GExpr $ mappend w1 w2


instance (Floating a, Monoid w, Eq w) => Interp__pi (MonoidRepr w) a where
  interp__pi = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__exp (MonoidRepr w) a where
  interp__exp = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__log (MonoidRepr w) a where
  interp__log = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__sqrt (MonoidRepr w) a where
  interp__sqrt = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__'times'times (MonoidRepr w) a where
  interp__'times'times = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__logBase (MonoidRepr w) a where
  interp__logBase = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__sin (MonoidRepr w) a where
  interp__sin = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__cos (MonoidRepr w) a where
  interp__cos = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__tan (MonoidRepr w) a where
  interp__tan = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__asin (MonoidRepr w) a where
  interp__asin = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__acos (MonoidRepr w) a where
  interp__acos = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__atan (MonoidRepr w) a where
  interp__atan = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__sinh (MonoidRepr w) a where
  interp__sinh = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__cosh (MonoidRepr w) a where
  interp__cosh = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__tanh (MonoidRepr w) a where
  interp__tanh = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__asinh (MonoidRepr w) a where
  interp__asinh = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__acosh (MonoidRepr w) a where
  interp__acosh = interp__'bottom

instance (Floating a, Monoid w, Eq w) => Interp__atanh (MonoidRepr w) a where
  interp__atanh = interp__'bottom


--
-- Probability operations
--

instance (Monoid w, Eq w) => Interp__realToProb (MonoidRepr w) where
  interp__realToProb = interp__'bottom

instance (Monoid w, Eq w) => Interp__logRealToProb (MonoidRepr w) where
  interp__logRealToProb = interp__'bottom

instance (Monoid w, Eq w) => Interp__probToReal (MonoidRepr w) where
  interp__probToReal = interp__'bottom

instance (Monoid w, Eq w) => Interp__probToLogReal (MonoidRepr w) where
  interp__probToLogReal = interp__'bottom

instance (Monoid w, Eq w) => Interp__gammaProb (MonoidRepr w) where
  interp__gammaProb = interp__'bottom

instance (Monoid w, Eq w) => Interp__digamma (MonoidRepr w) where
  interp__digamma = interp__'bottom


--
-- Misc operations
--

-- NOTE: because interp__'projADT, above, joins over all paths (including error
-- paths!), we need error paths to not signal a Haskell error inside MonoidRepr
instance (Monoid w, Eq w) => Interp__gerror (MonoidRepr w) a where
  interp__gerror = interp__'bottom
  -- interp__gerror = error "gerror called in MonoidRepr"
