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
{-# LANGUAGE TemplateHaskell #-}

module Language.Grappa.Interp.TypedExpr where

import Data.Proxy
import Data.Functor.Const

import qualified Language.Haskell.TH as TH

import Language.Grappa.Interp
import Language.Grappa.GrappaInternals
import Language.Haskell.TH.GrappaUtil


----------------------------------------------------------------------
-- * Typed TH Expressions
----------------------------------------------------------------------  

-- | Typed Template Haskell literals
data TypedLit a where
  TypedIntLit :: Num a => Integer -> TypedLit a
  TypedRatLit :: Fractional a => Rational -> TypedLit a

data TypedExpr a where
  TypedVar :: TH.Name -> TypedExpr a
  -- ^ A Haskell definition or variable lifted into the expression language
  TypedLit :: TypedLit a -> TypedExpr a
  -- ^ Literal expressions
  TypedApp :: TypedExpr (a -> b) -> TypedExpr a -> TypedExpr b
  -- ^ Function application
  TypedLam :: (TH.Name -> TypedExpr b) -> TypedExpr (a -> b)
  -- ^ Function abstraction
  TypedIfThenElse :: TypedExpr Bool -> TypedExpr a -> TypedExpr a -> TypedExpr a
  -- ^ If-then-else expression
  TypedFix :: (TH.Name -> TypedExpr a) -> TypedExpr a
  -- ^ Fixed-point expression

  TypedCtor :: THADT adt => adt TypedExpr (ADT adt) -> TypedExpr (ADT adt)
  -- ^ Constructor application expression
  TypedMatchCtor :: THADT adt => TypedExpr (ADT adt) ->
                    (adt Proxy (ADT adt)) ->
                    (adt (Const TH.Name) (ADT adt) -> TypedExpr a) ->
                    TypedExpr a -> TypedExpr a
  -- ^ ADT match expression against a specific constructor, given as an element
  -- of the ADT, that will either call the continuation if the expression
  -- matches the constructor or will call the alternative expression otherwise


----------------------------------------------------------------------
-- * Compiling to TH
----------------------------------------------------------------------

compileToTH :: TypedExpr a -> TH.Q TH.Exp
compileToTH (TypedVar nm) = TH.varE nm
compileToTH (TypedLit (TypedIntLit i)) = TH.litE (TH.IntegerL i)
compileToTH (TypedLit (TypedRatLit r)) = TH.litE (TH.RationalL r)
compileToTH (TypedApp f arg) = TH.appE (compileToTH f) (compileToTH arg)
compileToTH (TypedLam f) =
  do x <- TH.newName "x"
     TH.lamE [TH.varP x] (compileToTH (f x))
compileToTH (TypedIfThenElse c t f) =
  TH.condE (compileToTH c) (compileToTH t) (compileToTH f)
compileToTH (TypedFix f) =
  do x <- TH.newName "fix_var"
     TH.letE [TH.valD (TH.varP x) (TH.normalB $ compileToTH $ f x) []]
       (TH.varE x)
compileToTH (TypedCtor adt) =
  adtToTHExp <$> traverseADT (fmap Const . compileToTH) adt
compileToTH (TypedMatchCtor e ctor k_succ k_fail) =
  do ns_adt <- traverseADT (const (Const <$> TH.newName "ctor_arg")) ctor
     TH.caseE (compileToTH e)
       [TH.match (return $ adtToTHPattern ns_adt)
        (TH.normalB $ compileToTH $ k_succ $ ns_adt) []
       ,
        TH.match TH.wildP (TH.normalB $ compileToTH k_fail) []]


----------------------------------------------------------------------
-- * The Typed Expression Representation
----------------------------------------------------------------------

data TypedExprRepr :: *

instance ValidExprRepr TypedExprRepr where
  type GExprRepr TypedExprRepr a = TypedExpr a
  interp__'bottom = error "TypedExprRepr: unexpected bottom!"
  interp__'injTuple tup = GExpr $ TypedCtor $ mapADT unGExpr tup
  interp__'projTuple (GExpr e) k =
    GExpr $ TypedMatchCtor e (buildTuple Proxy)
    (unGExpr . k . mapADT (GExpr . TypedVar . getConst)) $
    error "TypedExprRepr: unexpected tuple match failure"
  interp__'app (GExpr f) (GExpr x) =
    GExpr (TypedApp f x)
  interp__'lam f = GExpr $ TypedLam (unGExpr . f . GExpr . TypedVar)
  interp__'fix f = GExpr $ TypedFix (unGExpr . f . GExpr . TypedVar)

instance THADT adt => Interp__ADT__Expr TypedExprRepr adt where
  interp__'injADT adt = GExpr $ TypedCtor $ mapADT unGExpr adt
  interp__'projADT (GExpr _e) _k =
    error "FIXME HERE: no support for projADT in TypedExprRepr!"
  interp__'projMatchADT (GExpr e) ctor _ k_succ k_fail =
    GExpr $ TypedMatchCtor e ctor
    (unGExpr . k_succ . mapADT (GExpr . TypedVar . getConst)) $
    unGExpr k_fail

-- | Helper for lifting definitions to 'TypedExpr'
typedVar :: TH.Name -> GExpr TypedExprRepr a
typedVar = GExpr . TypedVar


----------------------------------------------------------------------
-- * Interpreting the Operations
----------------------------------------------------------------------

--
-- Boolean and comparison operations
--

instance Interp__'ifThenElse TypedExprRepr where
  interp__'ifThenElse (GExpr c) (GExpr t) (GExpr f) =
    GExpr $ TypedIfThenElse c t f

instance Interp__not TypedExprRepr where
  interp__not = typedVar 'not

instance Interp__'amp'amp TypedExprRepr where
  interp__'amp'amp = typedVar '(&&)

instance Interp__'bar'bar TypedExprRepr where
  interp__'bar'bar = typedVar '(||)


instance Ord a => Interp__'eq'eq TypedExprRepr a where
  interp__'eq'eq = typedVar '(==)

instance Ord a => Interp__'lt TypedExprRepr a where
  interp__'lt = typedVar '(<)

instance Ord a => Interp__'gt TypedExprRepr a where
  interp__'gt = typedVar '(>)

instance Ord a => Interp__'lt'eq TypedExprRepr a where
  interp__'lt'eq = typedVar '(<=)

instance Ord a => Interp__'gt'eq TypedExprRepr a where
  interp__'gt'eq = typedVar '(>=)

instance Ord a => Interp__min TypedExprRepr a where
  interp__min = typedVar 'min

instance Ord a => Interp__max TypedExprRepr a where
  interp__max = typedVar 'max


instance Num a => Interp__'plus TypedExprRepr a where
  interp__'plus = typedVar '(+)

instance Num a => Interp__'minus TypedExprRepr a where
  interp__'minus = typedVar '(-)

instance Num a => Interp__'times TypedExprRepr a where
  interp__'times = typedVar '(*)

instance Num a => Interp__negate TypedExprRepr a where
  interp__negate = typedVar 'negate

instance Num a => Interp__abs TypedExprRepr a where
  interp__abs = typedVar 'abs

instance Num a => Interp__signum TypedExprRepr a where
  interp__signum = typedVar 'signum

instance Num a => Interp__fromInteger TypedExprRepr a where
  interp__fromInteger = typedVar 'fromInteger

instance Num a => Interp__'integer TypedExprRepr a where
  interp__'integer i = GExpr $ TypedLit $ TypedIntLit i

instance Fractional a => Interp__'rational TypedExprRepr a where
  interp__'rational r = GExpr $ TypedLit $ TypedRatLit r


instance Fractional a => Interp__'div TypedExprRepr a where
  interp__'div = typedVar '(/)

instance Fractional a => Interp__recip TypedExprRepr a where
  interp__recip = typedVar 'recip

instance Fractional a => Interp__fromRational TypedExprRepr a where
  interp__fromRational = typedVar 'fromRational


instance Floating a => Interp__pi TypedExprRepr a where
  interp__pi = typedVar 'pi

instance Floating a => Interp__exp TypedExprRepr a where
  interp__exp = typedVar 'exp

instance Floating a => Interp__log TypedExprRepr a where
  interp__log = typedVar 'log

instance Floating a => Interp__sqrt TypedExprRepr a where
  interp__sqrt = typedVar 'sqrt

instance Floating a => Interp__'times'times TypedExprRepr a where
  interp__'times'times = typedVar '(**)

instance Floating a => Interp__logBase TypedExprRepr a where
  interp__logBase = typedVar 'logBase

instance Floating a => Interp__sin TypedExprRepr a where
  interp__sin = typedVar 'sin

instance Floating a => Interp__cos TypedExprRepr a where
  interp__cos = typedVar 'cos

instance Floating a => Interp__tan TypedExprRepr a where
  interp__tan = typedVar 'tan

instance Floating a => Interp__asin TypedExprRepr a where
  interp__asin = typedVar 'asin

instance Floating a => Interp__acos TypedExprRepr a where
  interp__acos = typedVar 'acos

instance Floating a => Interp__atan TypedExprRepr a where
  interp__atan = typedVar 'atan

instance Floating a => Interp__sinh TypedExprRepr a where
  interp__sinh = typedVar 'sinh

instance Floating a => Interp__cosh TypedExprRepr a where
  interp__cosh = typedVar 'cosh

instance Floating a => Interp__tanh TypedExprRepr a where
  interp__tanh = typedVar 'tanh

instance Floating a => Interp__asinh TypedExprRepr a where
  interp__asinh = typedVar 'asinh

instance Floating a => Interp__acosh TypedExprRepr a where
  interp__acosh = typedVar 'acosh

instance Floating a => Interp__atanh TypedExprRepr a where
  interp__atanh = typedVar 'atanh


--
-- Probability operations
--

instance Interp__realToProb TypedExprRepr where
  interp__realToProb = typedVar 'realToProb

instance Interp__logRealToProb TypedExprRepr where
  interp__logRealToProb = typedVar 'logRealToProb

instance Interp__probToReal TypedExprRepr where
  interp__probToReal = typedVar 'probToReal

instance Interp__probToLogReal TypedExprRepr where
  interp__probToLogReal = typedVar 'probToLogReal

instance Interp__gammaProb TypedExprRepr where
  interp__gammaProb = typedVar 'gammaProb


--
-- Misc operations
--

instance Interp__gerror TypedExprRepr a where
  interp__gerror = typedVar 'gerror
