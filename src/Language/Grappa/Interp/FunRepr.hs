{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Grappa.Interp.FunRepr where

import Data.Proxy

import Language.Grappa.GrappaInternals
import Language.Grappa.Interp


--
-- * The Function Representation
--

-- | The function representation is like the reader monad, using the function
-- type @r -> a@ wherever the underlying representation uses @a@
data FunRepr r repr

-- | Build an underlying representation from a 'FunRepr' representation by
-- applying the latter to an argument
applyFunRepr :: r -> GExpr (FunRepr r repr) a -> GExpr repr a
applyFunRepr r (GExpr f) = GExpr $ f r

-- | Build a 'FunRepr' representation from an underlying representation by
-- abstracting over the argument and ignoring it
abstractFunRepr :: GExpr repr a -> GExpr (FunRepr r repr) a
abstractFunRepr (GExpr x) = GExpr $ \_ -> x

instance (ValidExprRepr repr) => ValidExprRepr (FunRepr r repr) where
  type GExprRepr (FunRepr r repr) a = (r -> GExprRepr repr a)

  interp__'bottom = abstractFunRepr interp__'bottom
  interp__'injTuple tup =
    GExpr $ \r -> unGExpr $ interp__'injTuple $ mapADT (applyFunRepr r) tup
  interp__'projTuple tup k =
    -- NOTE: the tuple gets passed the argument value at the site of the
    -- projection, and any argument values passed inside the k function get
    -- ignored (because we are using abstractFunRepr). This is again like
    -- pattern-matching on a tuple inside the reader monad, where you have to
    -- first bind the tuple and then do the pattern-match, so the resulting
    -- computations that are passed on ignore the reader argument.
    GExpr $ \r ->
    unGExpr (interp__'projTuple (applyFunRepr r tup)
             (applyFunRepr r . k . mapADT abstractFunRepr))
  interp__'app f x =
    GExpr $ \r -> unGExpr $ interp__'app (applyFunRepr r f) (applyFunRepr r x)
  interp__'lam f =
    -- NOTE: similarly to the projTuple case, the argument passed to f is a
    -- computation that ignores its argument
    GExpr $ \r ->
    unGExpr $ interp__'lam (applyFunRepr r . f . abstractFunRepr)
  interp__'fix f =
    -- NOTE: similarly to the projTuple case, the argument passed to f is a
    -- computation that ignores its argument
    GExpr $ \r ->
    unGExpr $ interp__'fix (applyFunRepr r . f . abstractFunRepr)

instance StrongTupleRepr repr => StrongTupleRepr (FunRepr r repr) where
  interp__'strongProjTuple e =
    untraverseTuple (\f -> GExpr (unGExpr . f)) $ \r ->
    interp__'strongProjTuple $ applyFunRepr r e

instance (TraversableADT adt, Interp__ADT__Expr repr adt) =>
         Interp__ADT__Expr (FunRepr r repr) adt where
  interp__'injADT adt =
    GExpr $ \r -> unGExpr $ interp__'injADT $ mapADT (applyFunRepr r) adt
  interp__'projADT adt k =
    -- NOTE: similarly to the projTuple case, the arguments passed to k are
    -- computations that ignore their argument
    GExpr $ \r ->
    unGExpr (interp__'projADT (applyFunRepr r adt)
             (applyFunRepr r . k . mapADT abstractFunRepr))

instance EmbedRepr repr a => EmbedRepr (FunRepr r repr) a where
  embedRepr a =
    GExpr $ \_ -> unGExpr (embedRepr a :: GExpr repr a)


----------------------------------------------------------------------
-- Interpreting the Operations
----------------------------------------------------------------------

--
-- Boolean and comparison operations
--

instance Interp__'ifThenElse repr => Interp__'ifThenElse (FunRepr r repr) where
  interp__'ifThenElse c t e =
    GExpr $ \r ->
    unGExpr $ interp__'ifThenElse (applyFunRepr r c) (applyFunRepr r t)
    (applyFunRepr r e)

instance Interp__not repr => Interp__not (FunRepr r repr) where
  interp__not = abstractFunRepr interp__not

instance Interp__'amp'amp repr => Interp__'amp'amp (FunRepr r repr) where
  interp__'amp'amp = abstractFunRepr interp__'amp'amp

instance Interp__'bar'bar repr => Interp__'bar'bar (FunRepr r repr) where
  interp__'bar'bar = abstractFunRepr interp__'bar'bar


instance Interp__'eq'eq repr a => Interp__'eq'eq (FunRepr r repr) a where
  interp__'eq'eq = abstractFunRepr interp__'eq'eq

instance Interp__'lt repr a => Interp__'lt (FunRepr r repr) a where
  interp__'lt = abstractFunRepr interp__'lt

instance Interp__'gt repr a => Interp__'gt (FunRepr r repr) a where
  interp__'gt = abstractFunRepr interp__'gt

instance Interp__'lt'eq repr a => Interp__'lt'eq (FunRepr r repr) a where
  interp__'lt'eq = abstractFunRepr interp__'lt'eq

instance Interp__'gt'eq repr a => Interp__'gt'eq (FunRepr r repr) a where
  interp__'gt'eq = abstractFunRepr interp__'gt'eq

instance Interp__min repr a => Interp__min (FunRepr r repr) a where
  interp__min = abstractFunRepr interp__min

instance Interp__max repr a => Interp__max (FunRepr r repr) a where
  interp__max = abstractFunRepr interp__max


instance Interp__'plus repr a => Interp__'plus (FunRepr r repr) a where
  interp__'plus = abstractFunRepr interp__'plus

instance Interp__'minus repr a => Interp__'minus (FunRepr r repr) a where
  interp__'minus = abstractFunRepr interp__'minus

instance Interp__'times repr a => Interp__'times (FunRepr r repr) a where
  interp__'times = abstractFunRepr interp__'times

instance Interp__negate repr a => Interp__negate (FunRepr r repr) a where
  interp__negate = abstractFunRepr interp__negate

instance Interp__abs repr a => Interp__abs (FunRepr r repr) a where
  interp__abs = abstractFunRepr interp__abs

instance Interp__signum repr a => Interp__signum (FunRepr r repr) a where
  interp__signum = abstractFunRepr interp__signum

instance Interp__fromInteger repr a =>
         Interp__fromInteger (FunRepr r repr) a where
  interp__fromInteger = abstractFunRepr interp__fromInteger

instance Interp__'integer repr a => Interp__'integer (FunRepr r repr) a where
  interp__'integer i = abstractFunRepr $ interp__'integer i

instance Interp__'eqInteger repr a =>
         Interp__'eqInteger (FunRepr r repr) a where
  interp__'eqInteger e1 e2 =
    GExpr $ \r ->
    unGExpr $ interp__'eqInteger (applyFunRepr r e1) (applyFunRepr r e2)

instance Interp__'rational repr a => Interp__'rational (FunRepr r repr) a where
  interp__'rational r = abstractFunRepr $ interp__'rational r

instance Interp__'eqRational repr a =>
         Interp__'eqRational (FunRepr r repr) a where
  interp__'eqRational e1 e2 =
    GExpr $ \r ->
    unGExpr $ interp__'eqRational (applyFunRepr r e1) (applyFunRepr r e2)


instance Interp__'div repr a => Interp__'div (FunRepr r repr) a where
  interp__'div = abstractFunRepr interp__'div

instance Interp__recip repr a => Interp__recip (FunRepr r repr) a where
  interp__recip = abstractFunRepr interp__recip

instance Interp__fromRational repr a =>
         Interp__fromRational (FunRepr r repr) a where
  interp__fromRational = abstractFunRepr interp__fromRational


instance Interp__pi repr a => Interp__pi (FunRepr r repr) a where
  interp__pi = abstractFunRepr interp__pi

instance Interp__exp repr a => Interp__exp (FunRepr r repr) a where
  interp__exp = abstractFunRepr interp__exp

instance Interp__log repr a => Interp__log (FunRepr r repr) a where
  interp__log = abstractFunRepr interp__log

instance Interp__sqrt repr a => Interp__sqrt (FunRepr r repr) a where
  interp__sqrt = abstractFunRepr interp__sqrt

instance Interp__'times'times repr a =>
         Interp__'times'times (FunRepr r repr) a where
  interp__'times'times = abstractFunRepr interp__'times'times

instance Interp__logBase repr a => Interp__logBase (FunRepr r repr) a where
  interp__logBase = abstractFunRepr interp__logBase

instance Interp__sin repr a => Interp__sin (FunRepr r repr) a where
  interp__sin = abstractFunRepr interp__sin

instance Interp__cos repr a => Interp__cos (FunRepr r repr) a where
  interp__cos = abstractFunRepr interp__cos

instance Interp__tan repr a => Interp__tan (FunRepr r repr) a where
  interp__tan = abstractFunRepr interp__tan

instance Interp__asin repr a => Interp__asin (FunRepr r repr) a where
  interp__asin = abstractFunRepr interp__asin

instance Interp__acos repr a => Interp__acos (FunRepr r repr) a where
  interp__acos = abstractFunRepr interp__acos

instance Interp__atan repr a => Interp__atan (FunRepr r repr) a where
  interp__atan = abstractFunRepr interp__atan

instance Interp__sinh repr a => Interp__sinh (FunRepr r repr) a where
  interp__sinh = abstractFunRepr interp__sinh

instance Interp__cosh repr a => Interp__cosh (FunRepr r repr) a where
  interp__cosh = abstractFunRepr interp__cosh

instance Interp__tanh repr a => Interp__tanh (FunRepr r repr) a where
  interp__tanh = abstractFunRepr interp__tanh

instance Interp__asinh repr a => Interp__asinh (FunRepr r repr) a where
  interp__asinh = abstractFunRepr interp__asinh

instance Interp__acosh repr a => Interp__acosh (FunRepr r repr) a where
  interp__acosh = abstractFunRepr interp__acosh

instance Interp__atanh repr a => Interp__atanh (FunRepr r repr) a where
  interp__atanh = abstractFunRepr interp__atanh


--
-- Probability operations
--

instance Interp__realToProb repr => Interp__realToProb (FunRepr r repr) where
  interp__realToProb = abstractFunRepr interp__realToProb

instance Interp__logRealToProb repr =>
         Interp__logRealToProb (FunRepr r repr) where
  interp__logRealToProb = abstractFunRepr interp__logRealToProb

instance Interp__probToReal repr => Interp__probToReal (FunRepr r repr) where
  interp__probToReal = abstractFunRepr interp__probToReal

instance Interp__probToLogReal repr =>
         Interp__probToLogReal (FunRepr r repr) where
  interp__probToLogReal = abstractFunRepr interp__probToLogReal

instance Interp__gammaProb repr => Interp__gammaProb (FunRepr r repr) where
  interp__gammaProb = abstractFunRepr interp__gammaProb


--
-- Misc operations
--

instance Interp__gerror repr a => Interp__gerror (FunRepr r repr) a where
  interp__gerror = abstractFunRepr interp__gerror
