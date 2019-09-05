{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Grappa.Interp.ProductRepr where

import Data.Proxy

import Language.Grappa.GrappaInternals
import Language.Grappa.Interp


--
-- * The Product Representation
--

-- | The product representation combines two representations as a pair
data ProductRepr repr1 repr2

-- | Build a product representation from representations of the components
mkProduct :: GExpr repr1 a -> GExpr repr2 a -> GExpr (ProductRepr repr1 repr2) a
mkProduct e1 e2 = GExpr (unGExpr e1, unGExpr e2)

-- | Wrapper around 'fst' for 'ProductRepr'
projProduct1 :: GExpr (ProductRepr repr1 repr2) a -> GExpr repr1 a
projProduct1 (GExpr (x, _)) = GExpr x

-- | Wrapper around 'snd' for 'ProductRepr'
projProduct2 :: GExpr (ProductRepr repr1 repr2) a -> GExpr repr2 a
projProduct2 (GExpr (_, y)) = GExpr y

-- | Embed the left representation into a 'ProductRepr', using bottom for the
-- right one
injProduct1 :: ValidExprRepr repr2 => Proxy repr2 -> GExpr repr1 a ->
               GExpr (ProductRepr repr1 repr2) a
injProduct1 (_ :: Proxy repr2) (GExpr x :: GExpr repr1 a) =
  GExpr (x, unGExpr (interp__'bottom :: GExpr repr2 a))

-- | Embed the right representation into a 'ProductRepr', using bottom for the
-- left one
injProduct2 :: ValidExprRepr repr1 => Proxy repr1 -> GExpr repr2 a ->
               GExpr (ProductRepr repr1 repr2) a
injProduct2 (_ :: Proxy repr1) (GExpr x :: GExpr repr2 a) =
  GExpr (unGExpr (interp__'bottom :: GExpr repr1 a), x)

-- | Take a function (which we assume is monotone) on pairs and split it into
-- functions on the two components, by passing in bottom for the other case when
-- needed
splitProductFun :: (ValidExprRepr repr1, ValidExprRepr repr2) =>
                   (GExpr (ProductRepr repr1 repr2) a ->
                    GExpr (ProductRepr repr1 repr2) b) ->
                   ((GExpr repr1 a -> GExpr repr1 b),
                    (GExpr repr2 a -> GExpr repr2 b))
splitProductFun f =
  ((projProduct1 . f . injProduct1 Proxy),
   (projProduct2 . f . injProduct2 Proxy))

instance (ValidExprRepr repr1, ValidExprRepr repr2) =>
         ValidExprRepr (ProductRepr repr1 repr2) where

  type GExprRepr (ProductRepr repr1 repr2) a =
    (GExprRepr repr1 a, GExprRepr repr2 a)

  interp__'bottom = injProduct1 Proxy interp__'bottom
  interp__'injTuple tup =
    GExpr (unGExpr $ interp__'injTuple $ mapADT projProduct1 tup,
           unGExpr $ interp__'injTuple $ mapADT projProduct2 tup)
  interp__'projTuple tup k =
    GExpr (unGExpr $
           interp__'projTuple (projProduct1 tup)
           (projProduct1 . k . mapADT (injProduct1 Proxy)),
           unGExpr $
           interp__'projTuple (projProduct2 tup)
           (projProduct2 . k . mapADT (injProduct2 Proxy)))
  interp__'app f x =
    GExpr (unGExpr $ interp__'app (projProduct1 f) (projProduct1 x),
           unGExpr $ interp__'app (projProduct2 f) (projProduct2 x))
  interp__'lam f =
    GExpr (unGExpr $ interp__'lam (fst (splitProductFun f)),
           unGExpr $ interp__'lam (snd (splitProductFun f)))
  interp__'fix f =
    GExpr (unGExpr $ interp__'fix (fst (splitProductFun f)),
           unGExpr $ interp__'fix (snd (splitProductFun f)))

instance (StrongTupleRepr repr1, StrongTupleRepr repr2) =>
         StrongTupleRepr (ProductRepr repr1 repr2) where
  interp__'strongProjTuple e =
    mapTuple2 (\e1 e2 -> GExpr (unGExpr e1, unGExpr e2))
    (interp__'strongProjTuple $ projProduct1 e)
    (interp__'strongProjTuple $ projProduct2 e)

instance (TraversableADT adt, Interp__ADT__Expr repr1 adt,
          Interp__ADT__Expr repr2 adt) =>
         Interp__ADT__Expr (ProductRepr repr1 repr2) adt where
  interp__'injADT adt =
    GExpr (unGExpr $ interp__'injADT $ mapADT projProduct1 adt,
           unGExpr $ interp__'injADT $ mapADT projProduct2 adt)
  interp__'projADT (GExpr (adt1, adt2)) k =
    GExpr (unGExpr $
           interp__'projADT (GExpr adt1)
           (projProduct1 . k . mapADT (injProduct1 Proxy))
          ,
           unGExpr $
           interp__'projADT (GExpr adt2)
           (projProduct2 . k . mapADT (injProduct2 Proxy)))
  interp__'projMatchADT adt ctor_proxy matcher k_succ k_fail =
    GExpr (unGExpr $
           interp__'projMatchADT (projProduct1 adt) ctor_proxy matcher
           (projProduct1 . k_succ . mapADT (injProduct1 Proxy))
           (projProduct1 k_fail)
          ,
           unGExpr $
           interp__'projMatchADT (projProduct2 adt) ctor_proxy matcher
           (projProduct2 . k_succ . mapADT (injProduct2 Proxy))
           (projProduct2 k_fail))

instance (EmbedRepr repr1 a, EmbedRepr repr2 a) =>
         EmbedRepr (ProductRepr repr1 repr2) a where
  embedRepr a = GExpr (unGExpr (embedRepr a :: GExpr repr1 a),
                       unGExpr (embedRepr a :: GExpr repr2 a))

----------------------------------------------------------------------
-- Interpreting the Operations
----------------------------------------------------------------------

--
-- Boolean and comparison operations
--

instance (Interp__'ifThenElse repr1, Interp__'ifThenElse repr2) =>
         Interp__'ifThenElse (ProductRepr repr1 repr2) where
  interp__'ifThenElse c t e =
    mkProduct (interp__'ifThenElse (projProduct1 c) (projProduct1 t)
               (projProduct1 e))
    (interp__'ifThenElse (projProduct2 c) (projProduct2 t)
               (projProduct2 e))

instance (Interp__not repr1, Interp__not repr2) =>
         Interp__not (ProductRepr repr1 repr2) where
  interp__not = mkProduct interp__not interp__not

instance (Interp__'amp'amp repr1, Interp__'amp'amp repr2) =>
         Interp__'amp'amp (ProductRepr repr1 repr2) where
  interp__'amp'amp = mkProduct interp__'amp'amp interp__'amp'amp

instance (Interp__'bar'bar repr1, Interp__'bar'bar repr2) =>
         Interp__'bar'bar (ProductRepr repr1 repr2) where
  interp__'bar'bar = mkProduct interp__'bar'bar interp__'bar'bar


instance (Interp__'eq'eq repr1 a, Interp__'eq'eq repr2 a) =>
         Interp__'eq'eq (ProductRepr repr1 repr2) a where
  interp__'eq'eq = mkProduct interp__'eq'eq interp__'eq'eq

instance (Interp__'lt repr1 a, Interp__'lt repr2 a) =>
         Interp__'lt (ProductRepr repr1 repr2) a where
  interp__'lt = mkProduct interp__'lt interp__'lt

instance (Interp__'gt repr1 a, Interp__'gt repr2 a) =>
         Interp__'gt (ProductRepr repr1 repr2) a where
  interp__'gt = mkProduct interp__'gt interp__'gt

instance (Interp__'lt'eq repr1 a, Interp__'lt'eq repr2 a) =>
         Interp__'lt'eq (ProductRepr repr1 repr2) a where
  interp__'lt'eq = mkProduct interp__'lt'eq interp__'lt'eq

instance (Interp__'gt'eq repr1 a, Interp__'gt'eq repr2 a) =>
         Interp__'gt'eq (ProductRepr repr1 repr2) a where
  interp__'gt'eq = mkProduct interp__'gt'eq interp__'gt'eq

instance (Interp__min repr1 a, Interp__min repr2 a) =>
         Interp__min (ProductRepr repr1 repr2) a where
  interp__min = mkProduct interp__min interp__min

instance (Interp__max repr1 a, Interp__max repr2 a) =>
         Interp__max (ProductRepr repr1 repr2) a where
  interp__max = mkProduct interp__max interp__max


--
-- Numeric operations
--

instance (Interp__'plus repr1 a, Interp__'plus repr2 a) =>
         Interp__'plus (ProductRepr repr1 repr2) a where
  interp__'plus = mkProduct interp__'plus interp__'plus

instance (Interp__'minus repr1 a, Interp__'minus repr2 a) =>
         Interp__'minus (ProductRepr repr1 repr2) a where
  interp__'minus = mkProduct interp__'minus interp__'minus

instance (Interp__'times repr1 a, Interp__'times repr2 a) =>
         Interp__'times (ProductRepr repr1 repr2) a where
  interp__'times = mkProduct interp__'times interp__'times

instance (Interp__negate repr1 a, Interp__negate repr2 a) =>
         Interp__negate (ProductRepr repr1 repr2) a where
  interp__negate = mkProduct interp__negate interp__negate

instance (Interp__abs repr1 a, Interp__abs repr2 a) =>
         Interp__abs (ProductRepr repr1 repr2) a where
  interp__abs = mkProduct interp__abs interp__abs

instance (Interp__signum repr1 a, Interp__signum repr2 a) =>
         Interp__signum (ProductRepr repr1 repr2) a where
  interp__signum = mkProduct interp__signum interp__signum

instance (Interp__fromInteger repr1 a, Interp__fromInteger repr2 a) =>
         Interp__fromInteger (ProductRepr repr1 repr2) a where
  interp__fromInteger = mkProduct interp__fromInteger interp__fromInteger

instance (Interp__'integer repr1 a, Interp__'integer repr2 a) =>
         Interp__'integer (ProductRepr repr1 repr2) a where
  interp__'integer i = mkProduct (interp__'integer i) (interp__'integer i)

instance (Interp__'eqInteger repr1 a, Interp__'eqInteger repr2 a) =>
         Interp__'eqInteger (ProductRepr repr1 repr2) a where
  interp__'eqInteger e1 e2 =
    mkProduct (interp__'eqInteger (projProduct1 e1) (projProduct1 e2))
    (interp__'eqInteger (projProduct2 e1) (projProduct2 e2))


instance (Interp__'div repr1 a, Interp__'div repr2 a) =>
         Interp__'div (ProductRepr repr1 repr2) a where
  interp__'div = mkProduct interp__'div interp__'div

instance (Interp__recip repr1 a, Interp__recip repr2 a) =>
         Interp__recip (ProductRepr repr1 repr2) a where
  interp__recip = mkProduct interp__recip interp__recip

instance (Interp__fromRational repr1 a, Interp__fromRational repr2 a) =>
         Interp__fromRational (ProductRepr repr1 repr2) a where
  interp__fromRational = mkProduct interp__fromRational interp__fromRational

instance (Interp__'rational repr1 a, Interp__'rational repr2 a) =>
         Interp__'rational (ProductRepr repr1 repr2) a where
  interp__'rational r = mkProduct (interp__'rational r) (interp__'rational r)

instance (Interp__'eqRational repr1 a, Interp__'eqRational repr2 a) =>
         Interp__'eqRational (ProductRepr repr1 repr2) a where
  interp__'eqRational e1 e2 =
    mkProduct (interp__'eqRational (projProduct1 e1) (projProduct1 e2))
    (interp__'eqRational (projProduct2 e1) (projProduct2 e2))


instance (Interp__pi repr1 a, Interp__pi repr2 a) =>
         Interp__pi (ProductRepr repr1 repr2) a where
  interp__pi = mkProduct interp__pi interp__pi

instance (Interp__exp repr1 a, Interp__exp repr2 a) =>
         Interp__exp (ProductRepr repr1 repr2) a where
  interp__exp = mkProduct interp__exp interp__exp

instance (Interp__log repr1 a, Interp__log repr2 a) =>
         Interp__log (ProductRepr repr1 repr2) a where
  interp__log = mkProduct interp__log interp__log

instance (Interp__sqrt repr1 a, Interp__sqrt repr2 a) =>
         Interp__sqrt (ProductRepr repr1 repr2) a where
  interp__sqrt = mkProduct interp__sqrt interp__sqrt

instance (Interp__'times'times repr1 a, Interp__'times'times repr2 a) =>
         Interp__'times'times (ProductRepr repr1 repr2) a where
  interp__'times'times = mkProduct interp__'times'times interp__'times'times

instance (Interp__logBase repr1 a, Interp__logBase repr2 a) =>
         Interp__logBase (ProductRepr repr1 repr2) a where
  interp__logBase = mkProduct interp__logBase interp__logBase

instance (Interp__sin repr1 a, Interp__sin repr2 a) =>
         Interp__sin (ProductRepr repr1 repr2) a where
  interp__sin = mkProduct interp__sin interp__sin

instance (Interp__cos repr1 a, Interp__cos repr2 a) =>
         Interp__cos (ProductRepr repr1 repr2) a where
  interp__cos = mkProduct interp__cos interp__cos

instance (Interp__tan repr1 a, Interp__tan repr2 a) =>
         Interp__tan (ProductRepr repr1 repr2) a where
  interp__tan = mkProduct interp__tan interp__tan

instance (Interp__asin repr1 a, Interp__asin repr2 a) =>
         Interp__asin (ProductRepr repr1 repr2) a where
  interp__asin = mkProduct interp__asin interp__asin

instance (Interp__acos repr1 a, Interp__acos repr2 a) =>
         Interp__acos (ProductRepr repr1 repr2) a where
  interp__acos = mkProduct interp__acos interp__acos

instance (Interp__atan repr1 a, Interp__atan repr2 a) =>
         Interp__atan (ProductRepr repr1 repr2) a where
  interp__atan = mkProduct interp__atan interp__atan

instance (Interp__sinh repr1 a, Interp__sinh repr2 a) =>
         Interp__sinh (ProductRepr repr1 repr2) a where
  interp__sinh = mkProduct interp__sinh interp__sinh

instance (Interp__cosh repr1 a, Interp__cosh repr2 a) =>
         Interp__cosh (ProductRepr repr1 repr2) a where
  interp__cosh = mkProduct interp__cosh interp__cosh

instance (Interp__tanh repr1 a, Interp__tanh repr2 a) =>
         Interp__tanh (ProductRepr repr1 repr2) a where
  interp__tanh = mkProduct interp__tanh interp__tanh

instance (Interp__asinh repr1 a, Interp__asinh repr2 a) =>
         Interp__asinh (ProductRepr repr1 repr2) a where
  interp__asinh = mkProduct interp__asinh interp__asinh

instance (Interp__acosh repr1 a, Interp__acosh repr2 a) =>
         Interp__acosh (ProductRepr repr1 repr2) a where
  interp__acosh = mkProduct interp__acosh interp__acosh

instance (Interp__atanh repr1 a, Interp__atanh repr2 a) =>
         Interp__atanh (ProductRepr repr1 repr2) a where
  interp__atanh = mkProduct interp__atanh interp__atanh


--
-- Probability operations
--

instance (Interp__realToProb repr1, Interp__realToProb repr2) =>
         Interp__realToProb (ProductRepr repr1 repr2) where
  interp__realToProb = mkProduct interp__realToProb interp__realToProb

instance (Interp__logRealToProb repr1, Interp__logRealToProb repr2) =>
         Interp__logRealToProb (ProductRepr repr1 repr2) where
  interp__logRealToProb = mkProduct interp__logRealToProb interp__logRealToProb

instance (Interp__probToReal repr1, Interp__probToReal repr2) =>
         Interp__probToReal (ProductRepr repr1 repr2) where
  interp__probToReal = mkProduct interp__probToReal interp__probToReal

instance (Interp__probToLogReal repr1, Interp__probToLogReal repr2) =>
         Interp__probToLogReal (ProductRepr repr1 repr2) where
  interp__probToLogReal = mkProduct interp__probToLogReal interp__probToLogReal

instance (Interp__gammaProb repr1, Interp__gammaProb repr2) =>
         Interp__gammaProb (ProductRepr repr1 repr2) where
  interp__gammaProb = mkProduct interp__gammaProb interp__gammaProb

instance (Interp__digamma repr1, Interp__digamma repr2) =>
         Interp__digamma (ProductRepr repr1 repr2) where
  interp__digamma = mkProduct interp__digamma interp__digamma


--
-- Misc operations
--

instance (Interp__gerror repr1 a, Interp__gerror repr2 a) =>
         Interp__gerror (ProductRepr repr1 repr2) a where
  interp__gerror = mkProduct interp__gerror interp__gerror
