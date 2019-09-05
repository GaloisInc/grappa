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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

module Language.Grappa.Interp.ADHORepr where

import Data.Proxy
import Unsafe.Coerce
import GHC.Exts

import Language.Grappa.Interp
import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals
import Language.Grappa.Frontend.DataSource
import Language.Grappa.Interp.StandardHORepr

import qualified Numeric.AD.Mode.Reverse as ADR
import qualified Numeric.AD.Internal.Reverse as ADR (Tape(..))
import qualified Data.Reflection as ADR (reflect, Reifies)

--import qualified Data.Matrix as M
import qualified Numeric.Log as Log


----------------------------------------------------------------------
-- * 'ADHORepr' as an Expression Representation
----------------------------------------------------------------------

-- | The type tag for the AD-ified higher-order representation, which is
-- parameterized by a container type @f@ that holds real-valued inputs and a
-- monad @m@
data ADHORepr (m :: * -> *) (f :: * -> *) :: *

-- | The "return type" for the ADHORepr representation
type ADHOReprRet m s = StandardHORepr m (ADR.Reverse s Double) Int

-- | The "return type" for the ADHORepr representation
type ADHOReprRetF m s a = StandardHOReprF m (ADR.Reverse s Double) Int a

-- | The type of AD-ified expressions relative to monad @m@ (which is used to
-- represent distributions). Conceptually, these are values that are computed
-- from some sequence of 'Double'-valued inputs, where the real-valued portions
-- have a computable gradient relative to the inputs.
newtype ADExpr m f a =
  ADExpr { unADExpr ::
             forall s. ADR.Reifies s ADR.Tape =>
             f (ADR.Reverse s Double) -> GExpr (ADHOReprRet m s) a }

-- | Apply an ADHORepr to a specific @s@ type variable
applyADExpr :: ADR.Reifies s ADR.Tape => f (ADR.Reverse s Double) ->
               GExpr (ADHORepr m f) a -> GExpr (ADHOReprRet m s) a
applyADExpr r (GExpr e) = unADExpr e r

-- | Coerce to a different "s" type argument in an AD-ified type by inserting a
-- runtime check that the two represent the same AD context
coerceSArg :: (ADR.Reifies s1 ADR.Tape, ADR.Reifies s2 ADR.Tape) =>
              Proxy s1 -> Proxy s2 ->
              f (ADHOReprRet m s1) a -> f (ADHOReprRet m s2) a
coerceSArg p1 p2 =
  if ADR.getTape (ADR.reflect p1) == ADR.getTape (ADR.reflect p2)
  then unsafeCoerce else error "coerceSArg"

-- | Abstract an ADHORepr by quantifying over all possible @s@ type
-- variables. This is only safe (where "safe" means we aren't accidentally
-- building junk terms) if end up applying it to the same @s@ type variable
-- anyway, which is checked by 'coerceSArg'
abstractADExpr :: ADR.Reifies s ADR.Tape =>
                  GExpr (ADHOReprRet m s) a -> GExpr (ADHORepr m f) a
abstractADExpr e =
  GExpr $ ADExpr $ \_ -> coerceSArg Proxy Proxy e

-- | Like a "run" method for 'ADHORepr': compute the gradient of a real-valued
-- expression
gradADHORepr :: Traversable f => GExpr (ADHORepr m f) R -> f Double -> f Double
gradADHORepr (GExpr (ADExpr f)) = ADR.grad $ unGExpr . f

-- | Like a "run" method for 'ADHORepr': compute the gradient of a real-valued
-- probability expression
gradProbADHORepr :: Traversable f => GExpr (ADHORepr m f) Prob ->
                    f Double -> f Double
gradProbADHORepr (GExpr (ADExpr f)) =
  ADR.grad $ Log.ln . unGExpr . f

instance ValidExprRepr (ADHORepr m f) where
  type GExprRepr (ADHORepr m f) a = ADExpr m f a

  interp__'bottom = error "ADHORepr: unexpected bottom!"
  interp__'injTuple !tup =
    GExpr $ ADExpr $ \r -> interp__'injTuple $ mapADT (applyADExpr r) tup
  interp__'projTuple tup k =
    -- NOTE: the tuple gets passed the @s@ type variable at the site of the
    -- projection, and any @s@ type variables passed inside the k function get
    -- ignored (because we are using abstractADExpr). This is like
    -- pattern-matching on a tuple inside the reader monad, where you have to
    -- first bind the tuple and then do the pattern-match, so the resulting
    -- computations that are passed on ignore the reader argument.
    GExpr $ ADExpr $ \r ->
    (interp__'projTuple (applyADExpr r tup)
     (applyADExpr r . k . mapADT abstractADExpr))
  interp__'app f x =
    GExpr $ ADExpr $ \r -> interp__'app (applyADExpr r f) (applyADExpr r x)
  interp__'lam f =
    -- NOTE: similarly to the projTuple case, the argument passed to f is a
    -- computation that ignores its @s@ type argument
    GExpr $ ADExpr $ \r -> interp__'lam (applyADExpr r . f . abstractADExpr)
  interp__'fix f =
    -- NOTE: similarly to the projTuple case, the argument passed to f is a
    -- computation that ignores its @s@ type argument
    GExpr $ ADExpr $ \r -> interp__'fix (applyADExpr r . f . abstractADExpr)


instance StrongTupleRepr (ADHORepr m f) where
  interp__'strongProjTuple =
    helper typeListProxy
    where
      helper :: TupleF bs proxy r -> GExpr (ADHORepr m f) (GTuple bs) ->
                TupleF bs (GExpr (ADHORepr m f)) r
      helper Tuple0 = \_ -> Tuple0
      helper tup@(Tuple1 _) = helperStep tup
      helper tup@(Tuple2 _ _) = helperStep tup
      helper tup@(Tuple3 _ _ _) = helperStep tup
      helper tup@(Tuple4 _ _ _ _) = helperStep tup
      helper tup@(TupleN _ _ _ _ _ _) = helperStep tup

      helperStep :: TupleF (b ': bs) proxy r ->
                    GExpr (ADHORepr m f) (GTuple (b ': bs)) ->
                    TupleF (b ': bs) (GExpr (ADHORepr m f)) r
      helperStep ts tup_e =
        tupleCons (GExpr $ ADExpr $ \r ->
                    tupleHead $ unGExpr $ applyADExpr r tup_e)
        (helper (tupleTail ts)
         (GExpr $ ADExpr $ \r ->
           GExpr $ tupleTail $ unGExpr $ applyADExpr r tup_e))


instance TraversableADT adt => Interp__ADT__Expr (ADHORepr m f) adt where
  interp__'injADT adt =
    GExpr $ ADExpr $ \r -> interp__'injADT $ mapADT (applyADExpr r) adt
  interp__'projADT adt k =
    -- NOTE: see disclaimer for the projTuple case, above
    GExpr $ ADExpr $ \r ->
    (interp__'projADT (applyADExpr r adt)
     (applyADExpr r . k . mapADT abstractADExpr))
  interp__'projMatchADT adt ctor matcher k_succ k_fail =
    -- NOTE: see disclaimer for the projTuple case, above
    GExpr $ ADExpr $ \r ->
    (interp__'projMatchADT (applyADExpr r adt) ctor matcher
     (applyADExpr r . k_succ . mapADT abstractADExpr)
     (applyADExpr r k_fail))


instance EmbedRepr (ADHORepr m f) R where
  embedRepr r = GExpr $ ADExpr $ \_ -> GExpr (ADR.auto r)
instance EmbedRepr (ADHORepr m f) Prob where
  embedRepr (Prob (Log.Exp r)) = GExpr $ ADExpr $ \_ ->
    GExpr $ Log.Exp (ADR.auto r)
instance EmbedRepr (ADHORepr m f) Int where
  embedRepr i = GExpr $ ADExpr $ \_ -> GExpr i
instance EmbedRepr (ADHORepr m f) Bool where
  embedRepr b = GExpr $ ADExpr $ \_ -> GExpr b


----------------------------------------------------------------------
-- * 'ADHORepr' as a Program Representation
----------------------------------------------------------------------

-- | The type of AD-ified statements relative to monad @m@
newtype ADStmt m f a =
  ADStmt { unADStmt ::
             forall s. ADR.Reifies s ADR.Tape =>
             f (ADR.Reverse s Double) -> GStmt (ADHOReprRet m s) a }

-- | Similar to 'applyADExpr' but for statements
applyADStmt :: ADR.Reifies s ADR.Tape => f (ADR.Reverse s Double) ->
               GStmt (ADHORepr m f) a -> GStmt (ADHOReprRet m s) a
applyADStmt r (GStmt e) = unADStmt e r

-- | Similar to 'abstractADExpr' but for statements
abstractADStmt :: ADR.Reifies s ADR.Tape =>
                  GStmt (ADHOReprRet m s) a -> GStmt (ADHORepr m f) a
abstractADStmt e = GStmt $ ADStmt $ \_ -> coerceSArg Proxy Proxy e

-- | Similar to 'applyADExpr' but for v-expressions (which is needed because
-- v-expressions could contain expressions)
applyADVExpr :: ADR.Reifies s ADR.Tape => f (ADR.Reverse s Double) ->
                GVExpr (ADHORepr m f) a -> GVExpr (ADHOReprRet m s) a
applyADVExpr _ (GVExpr VParam) = GVExpr VParam
applyADVExpr _ (GVExpr (VData d)) = GVExpr $ VData d
applyADVExpr r (GVExpr (VExpr e)) = GVExpr $ VExpr $ applyADExpr r e
applyADVExpr r (GVExpr (VADT adt)) =
  GVExpr $ VADT $ mapADT (unGVExpr . applyADVExpr r . GVExpr) adt

-- | Similar to 'abstractADExpr' but for v-expressions (which is needed because
-- v-expressions could contain expressions)
abstractADVExpr :: ADR.Reifies s ADR.Tape =>
                   GVExpr (ADHOReprRet m s) a -> GVExpr (ADHORepr m f) a
abstractADVExpr (GVExpr VParam) = GVExpr VParam
abstractADVExpr (GVExpr (VData d)) = GVExpr $ VData d
abstractADVExpr (GVExpr (VExpr e)) = GVExpr $ VExpr $ abstractADExpr e
abstractADVExpr (GVExpr (VADT adt)) =
  GVExpr $ VADT $ mapADT (unGVExpr . abstractADVExpr . GVExpr) adt

{-
-- | Helper to match on v-expressions in 'ADHORepr': if the 'DistVar' is not a
-- 'VParam', then destructure it and pass it to the continuation (the 2nd
-- argument); otherwise, return the failure continuation (the 3rd argument)
matchADHOReprADTDistVar ::
  TraversableADT adt =>
  DistVar (ADHORepr m f) (ADT adt) ->
  (adt (DistVar (ADHORepr m f)) (ADT adt) -> GStmt (ADHORepr m f) b) ->
  GStmt (ADHORepr m f) b ->
  GStmt (ADHORepr m f) b
matchADHOReprADTDistVar VParam _ ret = ret
matchADHOReprADTDistVar (VData (GData (ADT adt))) k _ =
  k $ mapADT (VData . GData . unId) adt
matchADHOReprADTDistVar (VData GNoData) _ ret = ret
matchADHOReprADTDistVar (VData (GADTData adt)) k _ = k $ mapADT VData adt
matchADHOReprADTDistVar (VExpr e) k _ =
  GStmt $ ADStmt $ \r ->
  applyADStmt r $ k $ mapADT abstractADExpr $ unGExpr (applyADExpr r e)
matchADHOReprADTDistVar (VADT adt) k _ = k adt
-}


instance Monad m => ValidRepr (ADHORepr m f) where
  type GVExprRepr (ADHORepr m f) a = DistVar (ADHORepr m f) a
  type GStmtRepr (ADHORepr m f) a = ADStmt m f a

  interp__'projTupleStmt tup k =
    GStmt $ ADStmt $ \r ->
    (interp__'projTupleStmt (applyADExpr r tup)
     (applyADStmt r . k . mapADT abstractADExpr))

  interp__'vInjTuple !tup =
    GVExpr (VADT $ mapADT unGVExpr tup)
  interp__'vProjTuple ve k =
    GStmt $ ADStmt $ \r ->
    (interp__'vProjTuple (applyADVExpr r ve)
     (applyADStmt r . k . mapADT abstractADVExpr))

  interp__'vwild k = k (GVExpr VParam)
  interp__'vlift e k = k (GVExpr $ VExpr e)

  interp__'return x = GStmt $ ADStmt $ \r -> interp__'return $ applyADExpr r x
  interp__'let rhs body =
    GStmt $ ADStmt $ \r ->
    interp__'let (applyADExpr r rhs) (applyADStmt r . body . abstractADExpr)
  interp__'sample d ve k =
    GStmt $ ADStmt $ \r ->
    interp__'sample (applyADExpr r d) (applyADVExpr r ve)
    (applyADStmt r . k . abstractADExpr)
  interp__'mkDist f =
    GExpr $ ADExpr $ \r ->
    interp__'mkDist (applyADStmt r . f . abstractADVExpr)


instance (Monad m, TraversableADT adt) => Interp__ADT (ADHORepr m f) adt where
  interp__'vInjADT adt = GVExpr (VADT $ mapADT unGVExpr adt)
  interp__'vProjMatchADT ve ctor matcher k_succ k_fail =
    GStmt $ ADStmt $ \r ->
    interp__'vProjMatchADT (applyADVExpr r ve) ctor matcher
    (applyADStmt r . k_succ . mapADT abstractADVExpr)
    (applyADStmt r k_fail)

instance Interp__'source (ADHORepr m f) a where
  interp__'source src =
    GVExpr . VData <$> interpSource src


----------------------------------------------------------------------
-- * Lifting Operations from 'StandardHORepr'
----------------------------------------------------------------------

{-
data ADExprC (c :: * -> Constraint) m s a where
  ADExprC :: c (ADHOReprRetF m s a) => ADExprC c m s a

class ADExprHasConstraint (c :: * -> Constraint) m a where
  adExprConstraint :: ADExprC c m s a

constrainedADExpr ::
  ADExprHasConstraint c m a => Proxy a -> Proxy c ->
  (forall s. (ADR.Reifies s ADR.Tape, c (ADHOReprRetF m s a)) =>
   GExpr (ADHOReprRet m s) b) ->
  GExpr (ADHORepr m f) b

constrainedADExpr pa pc e =
  GExpr $ ADExpr $
  case adExprConstraint of
    ADExprC -> e :: GExpr (ADHOReprRet m s) b
-}


-- | Typeclass stating that the 'ADExprRepr' representation satisfies class @c@
-- at type @a@. The method is CPS-translated to make it easier to use to form
-- 'ADExprRepr' expressions from expressions using 'StandardHORepr'.
class ADExprHasConstraint (c :: * -> Constraint) m a where
  constrainedADExpr ::
    Proxy a -> Proxy c ->
    (forall s. (ADR.Reifies s ADR.Tape, c (ADHOReprRetF m s a)) =>
     GExpr (ADHOReprRet m s) b) ->
    GExpr (ADHORepr m f) b

-- | Like 'ADExprHasConstraint' but for 2 constraints
{-
class ADExprHasConstraint2 (c1 c2 :: * -> Constraint) m a where
  constrainedADExpr ::
    Proxy a -> Proxy c ->
    (forall s. (ADR.Reifies s ADR.Tape,
                c1 (ADHOReprRetF m s a), c2 (ADHOReprRetF m s a)) =>
     GExpr (ADHOReprRet m s) b) ->
    GExpr (ADHORepr m f) b
-}

instance ADExprHasConstraint Eq m Double where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Ord m Double where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Num m Double where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Fractional m Double where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Floating m Double where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e


instance ADExprHasConstraint Eq m Prob where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Ord m Prob where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Num m Prob where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Fractional m Prob where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Floating m Prob where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e


instance ADExprHasConstraint Eq m Int where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Ord m Int where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e

instance ADExprHasConstraint Num m Int where
  constrainedADExpr _ _ e = GExpr $ ADExpr $ \_ -> e


----------------------------------------------------------------------
-- Boolean and Comparison Operations
----------------------------------------------------------------------

instance Interp__'ifThenElse (ADHORepr m f) where
  interp__'ifThenElse c t e =
    GExpr $ ADExpr $ \r ->
    interp__'ifThenElse (applyADExpr r c) (applyADExpr r t) (applyADExpr r e)

instance Interp__not (ADHORepr m f) where
  interp__not = GExpr $ ADExpr $ \_ -> interp__not

instance Interp__'amp'amp (ADHORepr m f) where
  interp__'amp'amp = GExpr $ ADExpr $ \_ -> interp__'amp'amp

instance Interp__'bar'bar (ADHORepr m f) where
  interp__'bar'bar = GExpr $ ADExpr $ \_ -> interp__'bar'bar


instance (Eq a, ADExprHasConstraint Eq m a) =>
         Interp__'eq'eq (ADHORepr m f) a where
  interp__'eq'eq =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Eq) interp__'eq'eq

instance (Ord a, ADExprHasConstraint Ord m a) =>
         Interp__'lt (ADHORepr m f) a where
  interp__'lt =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Ord) interp__'lt

instance (Ord a, ADExprHasConstraint Ord m a) =>
         Interp__'gt (ADHORepr m f) a where
  interp__'gt =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Ord) interp__'gt

instance (Ord a, ADExprHasConstraint Ord m a) =>
         Interp__'lt'eq (ADHORepr m f) a where
  interp__'lt'eq =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Ord) interp__'lt'eq

instance (Ord a, ADExprHasConstraint Ord m a) =>
         Interp__'gt'eq (ADHORepr m f) a where
  interp__'gt'eq =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Ord) interp__'gt'eq

instance (Ord a, ADExprHasConstraint Ord m a) =>
         Interp__min (ADHORepr m f) a where
  interp__min =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Ord) interp__min

instance (Ord a, ADExprHasConstraint Ord m a) =>
         Interp__max (ADHORepr m f) a where
  interp__max =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Ord) interp__max


----------------------------------------------------------------------
-- Numeric Operations
----------------------------------------------------------------------

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__'plus (ADHORepr m f) a where
  interp__'plus =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) interp__'plus

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__'minus (ADHORepr m f) a where
  interp__'minus =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) interp__'minus

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__'times (ADHORepr m f) a where
  interp__'times =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) interp__'times

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__negate (ADHORepr m f) a where
  interp__negate =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) interp__negate

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__abs (ADHORepr m f) a where
  interp__abs =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) interp__abs

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__signum (ADHORepr m f) a where
  interp__signum =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) interp__signum

instance (Num a, ADExprHasConstraint Num m a) =>
         Interp__'integer (ADHORepr m f) a where
  interp__'integer n =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Num) $
    interp__'integer n

instance (Eq a, Interp__'integer (ADHORepr m f) a, ADExprHasConstraint Eq m a)
         => Interp__'eqInteger (ADHORepr m f) a where
  interp__'eqInteger x y =
    interp__'app (interp__'app interp__'eq'eq x) y


--
-- Fractional typeclass
--

instance (Fractional a, ADExprHasConstraint Fractional m a) =>
         Interp__'div (ADHORepr m f) a where
  interp__'div =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Fractional) interp__'div

instance (Fractional a, ADExprHasConstraint Fractional m a) =>
         Interp__recip (ADHORepr m f) a where
  interp__recip =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Fractional)
    interp__recip

instance (Fractional a, ADExprHasConstraint Fractional m a) =>
         Interp__fromRational (ADHORepr m f) a where
  interp__fromRational =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Fractional)
    interp__fromRational

instance (Fractional a, ADExprHasConstraint Fractional m a) =>
         Interp__'rational (ADHORepr m f) a where
  interp__'rational n =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Fractional) $
    interp__'rational n

instance (Eq a, Interp__'rational (ADHORepr m f) a, ADExprHasConstraint Eq m a)
         => Interp__'eqRational (ADHORepr m f) a where
  interp__'eqRational x y =
    interp__'app (interp__'app interp__'eq'eq x) y


--
-- Floating typeclass
--

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__pi (ADHORepr m f) a where
  interp__pi =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__pi

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__exp (ADHORepr m f) a where
  interp__exp =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__exp

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__log (ADHORepr m f) a where
  interp__log =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__log

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__sqrt (ADHORepr m f) a where
  interp__sqrt =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__sqrt

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__'times'times (ADHORepr m f) a where
  interp__'times'times =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__'times'times

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__logBase (ADHORepr m f) a where
  interp__logBase =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__logBase

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__sin (ADHORepr m f) a where
  interp__sin =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__sin

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__cos (ADHORepr m f) a where
  interp__cos =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__cos

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__tan (ADHORepr m f) a where
  interp__tan =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__tan

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__asin (ADHORepr m f) a where
  interp__asin =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__asin

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__acos (ADHORepr m f) a where
  interp__acos =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__acos

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__atan (ADHORepr m f) a where
  interp__atan =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__atan

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__sinh (ADHORepr m f) a where
  interp__sinh =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__sinh

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__cosh (ADHORepr m f) a where
  interp__cosh =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__cosh

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__tanh (ADHORepr m f) a where
  interp__tanh =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__tanh

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__asinh (ADHORepr m f) a where
  interp__asinh =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__asinh

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__acosh (ADHORepr m f) a where
  interp__acosh =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__acosh

instance (Floating a, ADExprHasConstraint Floating m a) =>
         Interp__atanh (ADHORepr m f) a where
  interp__atanh =
    constrainedADExpr (Proxy :: Proxy a) (Proxy :: Proxy Floating)
    interp__atanh


----------------------------------------------------------------------
-- Probability expressions
----------------------------------------------------------------------

instance Interp__realToProb (ADHORepr m f) where
  interp__realToProb = GExpr $ ADExpr $ \_ -> interp__realToProb

instance Interp__logRealToProb (ADHORepr m f) where
  interp__logRealToProb = GExpr $ ADExpr $ \_ -> interp__logRealToProb

instance Interp__probToReal (ADHORepr m f) where
  interp__probToReal = GExpr $ ADExpr $ \_ -> interp__probToReal

instance Interp__probToLogReal (ADHORepr m f) where
  interp__probToLogReal = GExpr $ ADExpr $ \_ -> interp__probToLogReal

instance Interp__gammaProb (ADHORepr m f) where
  interp__gammaProb = GExpr $ ADExpr $ \_ -> interp__gammaProb

instance Interp__digamma (ADHORepr m f) where
  interp__digamma = GExpr $ ADExpr $ \_ -> interp__digamma

{-
instance (Show a, Show (ADExpr m f a), i ~ Int) =>
         Interp__gtrace (ADHORepr m f) a b where
  interp__gtrace = GExpr gtrace
-}


----------------------------------------------------------------------
-- Misc operations
----------------------------------------------------------------------

instance Interp__gerror (ADHORepr m f) a where
  interp__gerror = GExpr $ ADExpr $ \_ -> interp__gerror


----------------------------------------------------------------------
-- Distributions
----------------------------------------------------------------------

-- FIXME HERE: build a monad that draws the real values from the input vector
-- and the ints from a separate vector in the monad; then interpret all the
-- distributions
