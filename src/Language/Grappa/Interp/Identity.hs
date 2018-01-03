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

module Language.Grappa.Interp.Identity where

import GHC.Exts
import Language.Grappa.Distribution
import Language.Grappa.Model
import Language.Grappa.GrappaInternals
import Language.Grappa.Interp
import Language.Grappa.Frontend.DataSource

--
-- * The Identity Representation
--

data IdRepr (c :: * -> Constraint)

fromId :: forall a (c :: * -> Constraint). GExpr (IdRepr c) a -> GExprRepr (IdRepr c) a
fromId = unGExpr

fromIdModel :: forall a (c :: * -> Constraint). GStmt (IdRepr c) a -> GStmtRepr (IdRepr c) a
fromIdModel = unGStmt

type family IdReprF (c :: * -> Constraint) (a :: *) :: * where
  IdReprF c (a -> b) =
    IdReprF c a -> IdReprF c b
  IdReprF c (Dist' a) =
    DistVar a -> Model c (IdReprF c a)
  IdReprF c (ADT adt) =
    adt (GExpr (IdRepr c)) (ADT adt)
  IdReprF c Bool = IdReprF c GBool
  IdReprF c a = a

instance ValidExprRepr (IdRepr c) where
  type GExprRepr (IdRepr c) a = IdReprF c a
  interp__'bottom = error "IdRepr: unexpected bottom!"
  interp__'injTuple tup = GExpr tup
  interp__'projTuple (GExpr tup) k = k tup
  interp__'app (GExpr f) (GExpr x) = GExpr (f x)
  interp__'lam f = GExpr (unGExpr . f . GExpr)
  interp__'fix f = let x = f (interp__'fix f) in x

instance ValidRepr (IdRepr c) where
  type GVExprRepr (IdRepr c) a =
    DistVar a
  type GStmtRepr (IdRepr c) a =
    Model c (IdReprF c a)

  interp__'projTupleStmt (GExpr tup) k = k tup

  interp__'vInjTuple tup = GVExpr (VADT $ mapADT unGVExpr tup)
  interp__'vProjTuple (GVExpr (VADT tup)) k =
    k $ mapADT GVExpr tup
  interp__'vProjTuple (GVExpr VParam) k =
    k $ mapADT (\ _ -> GVExpr VParam) typeListProxy

  interp__'vwild k = k (GVExpr VParam)
  interp__'vlift _ _ = error "FIXME HERE: interp__'vlift"

  interp__'return (GExpr x) = GStmt (return x)
  interp__'let rhs body = body rhs
  interp__'sample (GExpr d) (GVExpr dv) k =
    GStmt $
    do x <- d dv
       unGStmt $ k (GExpr x)
  interp__'mkDist f = GExpr (\dv -> unGStmt $ f $ GVExpr dv)

instance TraversableADT adt => Interp__ADT__Expr (IdRepr c) adt where
  interp__'injADT adt = GExpr adt
  interp__'projADT (GExpr adt) k = k adt

instance TraversableADT adt => Interp__ADT (IdRepr c) adt where
  interp__'vInjADT adt = GVExpr (VADT $ mapADT unGVExpr adt)
  interp__'projADTStmt (GExpr adt) k = k adt

instance Interp__'source (IdRepr c) a where
  interp__'source src = do
    vexpr <- interpSource src
    return (GVExpr vexpr)

instance Interp__'ifThenElse (IdRepr c) where
  interp__'ifThenElse (GExpr c) t e =
    case c of TrueF -> t; FalseF -> e

instance (Eq a, Eq (IdReprF c a)) => Interp__'eq'eq (IdRepr c) a where
  interp__'eq'eq = GExpr (\ x y -> fromHaskellBool (x == y))

instance (Ord a, Ord (IdReprF c a)) => Interp__'lt (IdRepr c) a where
  interp__'lt = GExpr (\ x y -> fromHaskellBool (x < y))

instance (Ord a, Ord (IdReprF c a)) => Interp__'gt (IdRepr c) a where
  interp__'gt = GExpr (\ x y -> fromHaskellBool (x > y))

instance (Ord a, Ord (IdReprF c a)) => Interp__'lt'eq (IdRepr c) a where
  interp__'lt'eq = GExpr (\ x y -> fromHaskellBool (x <= y))

instance (Ord a, Ord (IdReprF c a)) => Interp__'gt'eq (IdRepr c) a where
  interp__'gt'eq = GExpr (\ x y -> fromHaskellBool (x >= y))

instance (Num a, Num (IdReprF c a)) => Interp__'plus (IdRepr c) a where
  interp__'plus = GExpr (+)

instance (Num a, Num (IdReprF c a)) => Interp__'minus (IdRepr c) a where
  interp__'minus = GExpr (-)

instance (Num a, Num (IdReprF c a)) => Interp__'times (IdRepr c) a where
  interp__'times = GExpr (*)

instance (Num a, Num (IdReprF c a)) => Interp__negate (IdRepr c) a where
  interp__negate = GExpr negate

instance (Num a, Num (IdReprF c a)) => Interp__abs (IdRepr c) a where
  interp__abs = GExpr abs

instance (Num a, Num (IdReprF c a)) => Interp__signum (IdRepr c) a where
  interp__signum = GExpr signum

instance (Fractional a, Fractional (IdReprF c a)) => Interp__'div (IdRepr c) a where
  interp__'div = GExpr (/)

instance (Floating a, Floating (IdReprF c a)) => Interp__'times'times (IdRepr c) a where
  interp__'times'times = GExpr (**)

instance (Floating a, Floating (IdReprF c a)) => Interp__sqrt (IdRepr c) a where
  interp__sqrt = GExpr sqrt

instance (Num a, Num (IdReprF c a)) => Interp__fromInteger (IdRepr c) a where
  interp__fromInteger = GExpr fromInteger

instance (Num a, Num (IdReprF c a), IsAtomic a ~ 'True)
         => Interp__'integer (IdRepr c) a where
  interp__'integer n = GExpr (fromInteger n)

instance (Fractional a, Fractional (IdReprF c a), IsAtomic a ~ 'True)
          => Interp__'rational (IdRepr c) a where
  interp__'rational n = GExpr (fromRational n)

instance (Interp__'integer (IdRepr c) a, Eq (IdReprF c a))
         => Interp__'eqInteger (IdRepr c) a where
  interp__'eqInteger (GExpr x) (GExpr y) = GExpr (fromHaskellBool (x == y))

instance (Interp__'rational (IdRepr c) a, Eq (IdReprF c a))
         => Interp__'eqRational (IdRepr c) a where
  interp__'eqRational (GExpr x) (GExpr y) = GExpr (fromHaskellBool (x == y))

instance (c Normal) => Interp__normal (IdRepr c) where
  interp__normal = GExpr normal

instance (c Uniform) => Interp__uniform (IdRepr c) where
  interp__uniform = GExpr uniform

instance (c Categorical) => Interp__categorical (IdRepr c) where
  interp__categorical = GExpr (categorical . mkList)
    where mkList :: GExprRepr (IdRepr c) (GList Prob) -> GList Prob
          mkList (Cons (GExpr x) (GExpr xs)) =
            ADT (Cons (Id x) (Id (mkList xs)))
          mkList Nil = ADT Nil

instance Interp__ctorDist__ListF (IdRepr c) where
  interp__ctorDist__Nil = GExpr ctorDist__Nil
  interp__ctorDist__Cons = GExpr ctorDist__Cons

instance c Categorical => Interp__adtDist__ListF (IdRepr c) where
  interp__adtDist__ListF = GExpr adtDist__ListF
