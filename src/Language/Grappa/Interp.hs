
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
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

module Language.Grappa.Interp where

import Data.Proxy
import Data.Maybe
import Data.Vector (Vector)
import Data.Aeson
import qualified Numeric.Log as Log

-- import qualified Numeric.AD.Mode.Forward as ADF
-- import qualified Numeric.AD.Mode.Reverse as ADR
-- import qualified Numeric.AD.Internal.Reverse as ADR (Tape)
-- import qualified Data.Reflection as ADR (Reifies)

import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals
import Language.Grappa.Frontend.DataSource

import Debug.Trace


----------------------------------------------------------------------
-- * Grappa Expression Types
----------------------------------------------------------------------

newtype GExpr repr a = GExpr { unGExpr :: GExprRepr repr a }
newtype GVExpr repr a = GVExpr { unGVExpr :: GVExprRepr repr a }
newtype GStmt repr a = GStmt { unGStmt :: GStmtRepr repr a }

instance GrappaShow (GExprRepr repr a) => GrappaShow (GExpr repr a) where
  grappaShow (GExpr x) = grappaShow x

instance GrappaShowListContents (GExprRepr repr a) =>
         GrappaShowListContents (GExpr repr a) where
  showListContents (GExpr x) = showListContents x

instance Eq (GExprRepr repr a) => Eq (GExpr repr a) where
  e1 == e2 = unGExpr e1 == unGExpr e2

instance FromJSON (GExprRepr repr a) => FromJSON (GExpr repr a) where
  parseJSON v = GExpr <$> parseJSON v


----------------------------------------------------------------------
-- * Valid Representations of Grappa Expressions
----------------------------------------------------------------------

-- | The class of valid representations of Grappa expressions
class ValidExprRepr (repr :: *) where
  type GExprRepr repr (a :: *) :: *

  -- NOTE: this is not used directly by the compiler
  interp__'bottom :: GExpr repr a

  -- Creating and projecting tuples
  interp__'injTuple :: TupleF ts (GExpr repr) (ADT (TupleF ts))
                    -> GExpr repr (GTuple ts)
  interp__'projTuple :: IsTypeList ts
                     => GExpr repr (GTuple ts)
                     -> (TupleF ts (GExpr repr) (ADT (TupleF ts)) -> GExpr repr r)
                     -> GExpr repr r

  -- Creating and applying functions
  interp__'app :: GExpr repr (a -> b) -> GExpr repr a -> GExpr repr b
  interp__'lam :: (GExpr repr a -> GExpr repr b) -> GExpr repr (a -> b)

  -- Fixed-points
  interp__'fix :: (GExpr repr a -> GExpr repr a) -> GExpr repr a


-- | The class of expression representations with strong tuples
class ValidExprRepr repr => StrongTupleRepr repr where
  -- NOTE: this is not used directly by the compiler
  interp__'strongProjTuple :: IsTypeList ts =>
                              GExpr repr (GTuple ts) ->
                              TupleF ts (GExpr repr) (ADT (TupleF ts))


----------------------------------------------------------------------
-- * Valid Representations of Grappa Programs
----------------------------------------------------------------------

-- | The class of valid representations of Grappa programs (including
-- expressions)
class ValidExprRepr repr => ValidRepr (repr :: *) where
  type GVExprRepr repr (a :: *) :: *
  type GStmtRepr repr (a :: *) :: *

  interp__'projTupleStmt ::
    IsTypeList ts => GExpr repr (GTuple ts) ->
    (TupleF ts (GExpr repr) (ADT (TupleF ts)) -> GStmt repr r) ->
    GStmt repr r

  -- v-expression constructs
  interp__'vInjTuple :: TupleF ts (GVExpr repr) (ADT (TupleF ts))
                     -> GVExpr repr (GTuple ts)
  interp__'vProjTuple ::
    IsTypeList ts => GVExpr repr (GTuple ts) ->
    (TupleF ts (GVExpr repr) (ADT (TupleF ts)) -> GStmt repr r) ->
    GStmt repr r

  interp__'vwild :: (GVExpr repr a -> GStmt repr b) -> GStmt repr b
  interp__'vlift :: GrappaType a => GExpr repr a ->
                    (GVExpr repr a -> GStmt repr b) -> GStmt repr b

  -- model statement constructs
  interp__'return :: GExpr repr b -> GStmt repr b
  interp__'let :: GExpr repr a -> (GExpr repr a -> GStmt repr b) -> GStmt repr b
  interp__'sample :: GExpr repr (Dist a) -> GVExpr repr a ->
                     (GExpr repr a -> GStmt repr b) -> GStmt repr b
  interp__'mkDist :: (GVExpr repr a -> GStmt repr a) -> GExpr repr (Dist a)


-- | The class of representations that can read variables from a data source
class Interp__'source repr a where
  interp__'source :: Source a -> IO (GVExpr repr a)


----------------------------------------------------------------------
-- * The Default Representation of Variable Expressions
----------------------------------------------------------------------

-- | Variables that are a combination of data (potentially with missing values)
-- and expressions that have been lifted to variables
data DistVar repr a where
  VParam :: DistVar repr a
  VData :: GrappaData a -> DistVar repr a
  VExpr :: GExpr repr a -> DistVar repr a
  VADT :: TraversableADT adt => adt (DistVar repr) (ADT adt) ->
          DistVar repr (ADT adt)

{- FIXME: this requires normal projADT...
-- | Match an 'ADT'-shaped 'DistVar'
matchADTDistVar :: TraversableADT adt => DistVar repr (ADT adt) ->
                   (adt (DistVar repr) (ADT adt) -> ret) -> ret -> ret
matchADTDistVar VParam _ ret = ret
matchADTDistVar (VData (ADT adt)) k _ = k $ mapADT (VData . unId) adt
matchADTDistVar (VADT adt) k _ = k adt
-}


----------------------------------------------------------------------
-- * Grappa Pattern-Matching
----------------------------------------------------------------------

-- | A pattern-matching computation over expressions. These intuitively
-- represent the body of a @case@ expression, encompassing zero or more branches
-- that can optionally match some set of inputs. The representation here is
-- similar in spirit to a CPS computation, where a failure continuation is taken
-- in as input. Any failure to match in a given @case@ expression body will fail
-- over to the next alternative branch by returning the failure continuation.
newtype GMatch repr a = GMatch { unGMatch :: GExpr repr a -> GExpr repr a }

-- | Build a pattern-matching expression from a @case@ expression body
interp__'match :: ValidExprRepr repr => GMatch repr a -> GExpr repr a
interp__'match (GMatch m) = m interp__'bottom

-- | Build a @case@ expression body that always succeeds and returns the given
-- body of the @case@ expression
interp__'matchBody :: GExpr repr a -> GMatch repr a
interp__'matchBody body = GMatch $ \_ -> body

-- | Build a @case@ expression body that always fails
interp__'matchFail :: GMatch repr a
interp__'matchFail = GMatch $ \k_fail -> k_fail

-- | Build a disjunctive @case@ expression body that tries the first @case@
-- expression body and then, if that fails, tries the second
interp__'matchDisj :: GMatch repr a -> GMatch repr a -> GMatch repr a
interp__'matchDisj (GMatch m1) (GMatch m2) =
  GMatch $ \k_fail -> m1 (m2 k_fail)

-- | Build a @case@ expression body with a Boolean guard
interp__'matchGuard :: Interp__'ifThenElse repr => GExpr repr Bool ->
                       GMatch repr a -> GMatch repr a
interp__'matchGuard g (GMatch m) =
  GMatch $ \k_fail -> interp__'ifThenElse g (m k_fail) k_fail

-- | Build a @case@ expression body that matches on a tuple
interp__'matchTuple ::
  (ValidExprRepr repr, IsTypeList ts) =>
  GExpr repr (ADT (TupleF ts)) ->
  (TupleF ts (GExpr repr) (ADT (TupleF ts)) -> GMatch repr a) ->
  GMatch repr a
interp__'matchTuple e k_succ =
  GMatch $ \k_fail ->
  interp__'projTuple e (\tup -> unGMatch (k_succ tup) k_fail)

-- | Build a pattern-matching @case@ expression body that tries to match an
-- expression (the 1st argument) against a constructor pattern (given as a
-- constructor application in the 2nd argument and as a pattern-matching
-- function in the 3rd argument). If the match is successful, the arguments of
-- the constructor are passed to the 4th argument.
interp__'matchADT ::
  (GrappaType a, Interp__ADT__Expr repr adt) =>
  GExpr repr (ADT adt) -> adt Proxy (ADT adt) -> CtorMatcher adt ->
  (adt (GExpr repr) (ADT adt) -> GMatch repr a) ->
  GMatch repr a
interp__'matchADT e ctor_proxy matcher k_succ =
  GMatch $ \k_fail ->
  (interp__'projMatchADT e ctor_proxy matcher $ \adt ->
    unGMatch (k_succ adt) k_fail)
  k_fail

-- | The class of expression representations that can handle a specific @adt@
class ValidExprRepr repr =>
      Interp__ADT__Expr (repr :: *) (adt :: (* -> *) -> * -> *) where
  interp__'injADT :: adt (GExpr repr) (ADT adt) -> GExpr repr (ADT adt)

  -- FIXME HERE NOW: remove projADT!
  interp__'projADT :: GrappaType a => GExpr repr (ADT adt) ->
                      (adt (GExpr repr) (ADT adt) -> GExpr repr a) ->
                      GExpr repr a

  -- | Test if an ADT expression matches a given constructor (specified by the
  -- 2nd and 3rd arguments), and if so, pass it to the "success continuation"
  -- (the 4th argument), and otherwise return the "failure continuation" (the
  -- 5th argument)
  interp__'projMatchADT ::
    GrappaType a => GExpr repr (ADT adt) ->
    adt Proxy (ADT adt) -> CtorMatcher adt ->
    (adt (GExpr repr) (ADT adt) -> GExpr repr a) -> GExpr repr a ->
    GExpr repr a


----------------------------------------------------------------------
-- * Pattern-Matching over V-Expressions
----------------------------------------------------------------------

-- | The type of the body of a @case@ statement at the model level, represented
-- as the CPS translation of a list of cases that may or may not match the
-- current input along with their probabilities
newtype GVMatch repr a =
  GVMatch { unGVMatch ::
              ([(GExpr repr Prob, Maybe (GStmt repr a))] -> GStmt repr a) ->
              GStmt repr a }

-- | The type of a single @case@ statement branch, represented as the CPS
-- translation of a statement that may or may not match the current input
newtype GVMatchOne repr a =
  GVMatchOne { unGVMatchOne ::
                 (Maybe (GStmt repr a) -> GStmt repr a) -> GStmt repr a }

-- | Class for interpreting a form of @switch@ statement over 'Int' expressions,
-- which returns the @i@th expression for 'Int' @i@, that is used in @model@
-- expressions that must choose between multiple alternatives
class ValidRepr repr => Interp__'vmatchSwitch repr where
  interp__'vmatchSwitch :: GExpr repr Int -> [GStmt repr a] -> GStmt repr a

-- | Build a pattern-matching statement from a @case@ statement body with only
-- one alternative
interp__'vmatch1 :: GVMatchOne repr a -> GStmt repr a
interp__'vmatch1 (GVMatchOne m) = m helper where
  helper (Just stmt) = stmt
  helper Nothing = error "Model case did not match input!"

-- | Collect the requirements for 'interp__'vmatch' into a single typeclass
class (Interp__categorical repr, Interp__'vmatchSwitch repr,
       Interp__'integer repr Prob, Interp__'integer repr Int,
       Interp__'plus repr Prob, Interp__'div repr Prob,
       Interp__ADT__Expr repr (ListF Prob)) =>
      Interp__'vmatch repr where

instance (Interp__categorical repr, Interp__'vmatchSwitch repr,
          Interp__'integer repr Prob, Interp__'integer repr Int,
          Interp__'plus repr Prob, Interp__'div repr Prob,
          Interp__ADT__Expr repr (ListF Prob)) =>
         Interp__'vmatch repr where

-- | Build a pattern-matching statement from a @case@ statement body
interp__'vmatch :: Interp__'vmatch repr => GVMatch repr a -> GStmt repr a
interp__'vmatch (GVMatch m) = m helper where
  -- helper :: [(GExpr repr Prob, Maybe (GStmt repr a))] -> GStmt repr a
  helper [] = error "interp__'vmatch: no cases in model!"
  helper ps_ms =
    -- Extract the probability exprs for the cases that do and don't match, and
    -- also get those cases that do match
    let (yes_ps, no_ps) = get_split_ps ps_ms
        expr_plus e1 e2 = interp__'app (interp__'app interp__'plus e1) e2
        expr_div e1 e2 = interp__'app (interp__'app interp__'div e1) e2
        yes_sum = foldr expr_plus (interp__'integer 0) yes_ps
        no_sum = foldr expr_plus (interp__'integer 0) no_ps
        total_sum = expr_plus yes_sum no_sum
        yes_norm = expr_div yes_sum total_sum
        no_norm = expr_div no_sum total_sum
        branches = catMaybes $ map snd ps_ms in
    -- Sample two variables: one for choosing the set of cases that do match out
    -- of all the possible matches, which is represented by sampling a known 0
    -- value from the categorical distribution with the weights
    -- [yes_sum/total_sum, no_sum/total_sum]; and a second variable for choosing
    -- among the cases that do match, which is represented by samplng an unknown
    -- value from the categorical distribution [yes_1, .., yes_n]
    interp__'vlift (interp__'integer 0) $ \vexp_0 ->
    interp__'vwild $ \vexp_wild ->
    interp__'sample (expr_categorical [yes_norm, no_norm]) vexp_0 $ \_ ->
    case branches of
      [] -> error "No cases match in model expression!"
      [branch] -> branch
      _ ->
        interp__'sample (expr_categorical yes_ps) vexp_wild $ \branch_num ->
        interp__'vmatchSwitch branch_num branches

  get_split_ps :: [(a, Maybe b)] -> ([a], [a])
  get_split_ps =
    foldr (\(a, maybe_b) (yes_l, no_l) ->
            maybe (a:yes_l, no_l) (const (yes_l, a:no_l)) maybe_b) ([],[])

  expr_categorical :: (Interp__categorical repr,
                       Interp__ADT__Expr repr (ListF Prob)) =>
                      [GExpr repr Prob] -> GExpr repr (Dist Int)
  expr_categorical =
    interp__'app interp__categorical .
    foldr (\p ps -> interp__'injADT $ Cons p ps) (interp__'injADT Nil)


-- | Build a @case@ statement branch that always succeeds and returns the given
-- statement
interp__'vmatchBody :: GStmt repr a -> GVMatchOne repr a
interp__'vmatchBody body = GVMatchOne $ \k -> k $ Just body

-- | Build an empty @case@ statement, with no branches
interp__'vmatchFail :: GVMatch repr a
interp__'vmatchFail = GVMatch $ \k -> k []

-- | Build a disjunctive @case@ statement body that tries the first @case@
-- statement body with a given probability and combines it with the remaining
-- @case@ statement body
interp__'vmatchDisj :: GExpr repr Prob -> GVMatchOne repr a ->
                       GVMatch repr a -> GVMatch repr a
interp__'vmatchDisj p (GVMatchOne m1) (GVMatch m2) =
  GVMatch $ \k1 ->
  m1 (\maybe_s -> m2 (\ps_ms -> k1 ((p, maybe_s) : ps_ms)))

-- | Build a @case@ statement branch with a Boolean guard
interp__'vmatchGuard :: Interp__'ifThenElseStmt repr => GExpr repr Bool ->
                        GVMatchOne repr a -> GVMatchOne repr a
interp__'vmatchGuard g (GVMatchOne m) =
  GVMatchOne $ \k_fail -> interp__'ifThenElseStmt g (m k_fail) (k_fail Nothing)

-- | Build a @case@ statement branch that matches on a tuple
interp__'vmatchTuple ::
  (ValidRepr repr, IsTypeList ts) =>
  GVExpr repr (ADT (TupleF ts)) ->
  (TupleF ts (GVExpr repr) (ADT (TupleF ts)) -> GVMatchOne repr a) ->
  GVMatchOne repr a
interp__'vmatchTuple ve k_succ =
  GVMatchOne $ \k_fail ->
  interp__'vProjTuple ve (\tup -> unGVMatchOne (k_succ tup) k_fail)

-- | Build a pattern-matching @case@ statement branch that tries to match an
-- expression (the 1st argument) against a constructor pattern (given as a
-- constructor application in the 2nd argument and as a pattern-matching
-- function in the 3rd argument). If the match is successful, the arguments of
-- the constructor are passed to the 4th argument.
interp__'vmatchADT ::
  (GrappaType a, Interp__ADT repr adt) =>
  GVExpr repr (ADT adt) -> adt Proxy (ADT adt) -> CtorMatcher adt ->
  (adt (GVExpr repr) (ADT adt) -> GVMatchOne repr a) ->
  GVMatchOne repr a
interp__'vmatchADT vexpr ctor_proxy matcher k_succ =
  GVMatchOne $ \k_fail ->
  interp__'vProjMatchADT vexpr ctor_proxy matcher
  (\adt -> unGVMatchOne (k_succ adt) k_fail) (k_fail Nothing)

-- | The class of program representations that can handle a specific @adt@
class (ValidRepr repr, Interp__ADT__Expr repr adt) =>
      Interp__ADT (repr :: *) (adt :: (* -> *) -> * -> *) where
  interp__'vInjADT :: adt (GVExpr repr) (ADT adt) -> GVExpr repr (ADT adt)

  -- | Build a pattern-matching @case@ statement branch that tries to match an
  -- expression (the 1st argument) against a constructor pattern (given as a
  -- constructor application in the 2nd argument and as a pattern-matching
  -- function in the 3rd argument). If the match is successful, the arguments of
  -- the constructor are passed to the 4th argument, and otherwise the 5th
  -- argument is returned.
  interp__'vProjMatchADT ::
    GrappaType a => GVExpr repr (ADT adt) ->
    adt Proxy (ADT adt) -> CtorMatcher adt ->
    (adt (GVExpr repr) (ADT adt) -> GStmt repr a) -> GStmt repr a ->
    GStmt repr a


----------------------------------------------------------------------
-- * Interpreting Boolean Expressions
----------------------------------------------------------------------

class ValidExprRepr repr => Interp__'ifThenElse repr where
  interp__'ifThenElse :: GExpr repr Bool -> GExpr repr a -> GExpr repr a ->
                         GExpr repr a

class ValidRepr repr => Interp__'ifThenElseStmt repr where
  interp__'ifThenElseStmt :: GExpr repr Bool -> GStmt repr a -> GStmt repr a ->
                             GStmt repr a

class (ValidExprRepr repr) => Interp__not repr where
  interp__not :: GExpr repr (Bool -> Bool)

class (ValidExprRepr repr) => Interp__'amp'amp repr where
  interp__'amp'amp :: GExpr repr (Bool -> Bool -> Bool)

class (ValidExprRepr repr) => Interp__'bar'bar repr where
  interp__'bar'bar :: GExpr repr (Bool -> Bool -> Bool)


----------------------------------------------------------------------
-- * Interpreting Comparison Expressions
----------------------------------------------------------------------

class (Eq a, ValidExprRepr repr) => Interp__'eq'eq repr a where
  interp__'eq'eq :: GExpr repr (a -> a -> Bool)

class (Ord a, ValidExprRepr repr) => Interp__'lt repr a where
  interp__'lt :: GExpr repr (a -> a -> Bool)

class (Ord a, ValidExprRepr repr) => Interp__'gt repr a where
  interp__'gt :: GExpr repr (a -> a -> Bool)

class (Ord a, ValidExprRepr repr) => Interp__'lt'eq repr a where
  interp__'lt'eq :: GExpr repr (a -> a -> Bool)

class (Ord a, ValidExprRepr repr) => Interp__'gt'eq repr a where
  interp__'gt'eq :: GExpr repr (a -> a -> Bool)

class (Ord a, ValidExprRepr repr) => Interp__min repr a where
  interp__min :: GExpr repr (a -> a -> a)

class (Ord a, ValidExprRepr repr) => Interp__max repr a where
  interp__max :: GExpr repr (a -> a -> a)

-- | Helper function for building comparison expressions
interp__ifLessThan :: (Interp__'ifThenElse repr, Interp__'lt repr a) =>
                      GExpr repr a -> GExpr repr a ->
                      GExpr repr b -> GExpr repr b -> GExpr repr b
interp__ifLessThan x ub e1 e2 =
  interp__'ifThenElse (interp__'app (interp__'app interp__'lt x) ub) e1 e2

-- | Helper function for building comparison expressions
interp__ifLessThanEq :: (Interp__'ifThenElse repr, Interp__'lt'eq repr a) =>
                        GExpr repr a -> GExpr repr a ->
                        GExpr repr b -> GExpr repr b -> GExpr repr b
interp__ifLessThanEq x ub e1 e2 =
  interp__'ifThenElse (interp__'app (interp__'app interp__'lt'eq x) ub) e1 e2


----------------------------------------------------------------------
-- * Interpreting Numeric Expressions
----------------------------------------------------------------------

class (Num a, ValidExprRepr repr) => Interp__'plus repr a where
  interp__'plus :: GExpr repr (a -> a -> a)

class (Num a, ValidExprRepr repr) => Interp__'minus repr a where
  interp__'minus :: GExpr repr (a -> a -> a)

class (Num a, ValidExprRepr repr) => Interp__'times repr a where
  interp__'times :: GExpr repr (a -> a -> a)

class (Num a, ValidExprRepr repr) => Interp__negate repr a where
  interp__negate :: GExpr repr (a -> a)

class (Num a, ValidExprRepr repr) => Interp__abs repr a where
  interp__abs :: GExpr repr (a -> a)

class (Num a, ValidExprRepr repr) => Interp__signum repr a where
  interp__signum :: GExpr repr (a -> a)

class (Num a, ValidExprRepr repr) => Interp__fromInteger repr a where
  interp__fromInteger :: GExpr repr (Integer -> a)

class (Num a, ValidExprRepr repr) => Interp__'integer repr a where
  interp__'integer :: Integer -> GExpr repr a

-- | This is used for pattern-matching against literal integers
class (Interp__'integer repr a) => Interp__'eqInteger repr a where
  interp__'eqInteger :: GExpr repr a -> GExpr repr a -> GExpr repr Bool

class (Integral a, ValidExprRepr repr) => Interp__quot repr a where
  interp__quot :: GExpr repr (a -> a -> a)

class (Integral a, ValidExprRepr repr) => Interp__rem repr a where
  interp__rem :: GExpr repr (a -> a -> a)

class (Integral a, ValidExprRepr repr) => Interp__div repr a where
  interp__div :: GExpr repr (a -> a -> a)

class (Integral a, ValidExprRepr repr) => Interp__mod repr a where
  interp__mod :: GExpr repr (a -> a -> a)

class (Integral a, ValidExprRepr repr) => Interp__toInteger repr a where
  interp__toInteger :: GExpr repr (a -> Integer)

class (Fractional a, ValidExprRepr repr) => Interp__'div repr a where
  interp__'div :: GExpr repr (a -> a -> a)

class (Fractional a, ValidExprRepr repr) => Interp__recip repr a where
  interp__recip :: GExpr repr (a -> a)

class (Fractional a, ValidExprRepr repr) => Interp__fromRational repr a where
  interp__fromRational :: GExpr repr (Rational -> a)

class (Fractional a, ValidExprRepr repr) => Interp__'rational repr a where
  interp__'rational :: Rational -> GExpr repr a

-- | This is used for pattern-matching against literal rational expressions
class (Interp__'rational repr a) => Interp__'eqRational repr a where
  interp__'eqRational :: GExpr repr a -> GExpr repr a -> GExpr repr Bool


class (Floating a, ValidExprRepr repr) => Interp__pi repr a where
  interp__pi :: GExpr repr a

class (Floating a, ValidExprRepr repr) => Interp__exp repr a where
  interp__exp :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__log repr a where
  interp__log :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__sqrt repr a where
  interp__sqrt :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__'times'times repr a where
  interp__'times'times :: GExpr repr (a -> a -> a)

class (Floating a, ValidExprRepr repr) => Interp__logBase repr a where
  interp__logBase :: GExpr repr (a -> a -> a)

class (Floating a, ValidExprRepr repr) => Interp__sin repr a where
  interp__sin :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__cos repr a where
  interp__cos :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__tan repr a where
  interp__tan :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__asin repr a where
  interp__asin :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__acos repr a where
  interp__acos :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__atan repr a where
  interp__atan :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__sinh repr a where
  interp__sinh :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__cosh repr a where
  interp__cosh :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__tanh repr a where
  interp__tanh :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__asinh repr a where
  interp__asinh :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__acosh repr a where
  interp__acosh :: GExpr repr (a -> a)

class (Floating a, ValidExprRepr repr) => Interp__atanh repr a where
  interp__atanh :: GExpr repr (a -> a)


instance (Interp__'plus repr a, Interp__'minus repr a, Interp__'times repr a,
          Interp__negate repr a, Interp__abs repr a, Interp__signum repr a,
          Interp__'integer repr a) =>
         Num (GExpr repr a) where
  (+) = interp__'app . interp__'app interp__'plus
  (-) = interp__'app . interp__'app interp__'minus
  (*) = interp__'app . interp__'app interp__'times
  negate = interp__'app interp__negate
  abs = interp__'app interp__abs
  signum = interp__'app interp__signum
  fromInteger = interp__'integer

instance (Num (GExpr repr a), Interp__'div repr a, Interp__recip repr a,
          Interp__'rational repr a) =>
         Fractional (GExpr repr a) where
  (/) = interp__'app . interp__'app interp__'div
  recip = interp__'app interp__recip
  fromRational = interp__'rational


instance (Fractional (GExpr repr a),
          Interp__pi repr a, Interp__exp repr a, Interp__log repr a,
          Interp__sqrt repr a, Interp__'times'times repr a,
          Interp__logBase repr a, Interp__sin repr a, Interp__cos repr a,
          Interp__asin repr a, Interp__acos repr a, Interp__atan repr a,
          Interp__sinh repr a, Interp__cosh repr a, Interp__asinh repr a,
          Interp__acosh repr a, Interp__atanh repr a) =>
         Floating (GExpr repr a) where
  pi = interp__pi
  exp = interp__'app interp__exp
  log = interp__'app interp__log
  sqrt = interp__'app interp__sqrt
  (**) = interp__'app . interp__'app interp__'times'times
  logBase = interp__'app . interp__'app interp__logBase
  sin = interp__'app interp__sin
  cos = interp__'app interp__cos
  asin = interp__'app interp__asin
  acos = interp__'app interp__acos
  atan = interp__'app interp__atan
  sinh = interp__'app interp__sinh
  cosh = interp__'app interp__cosh
  asinh = interp__'app interp__asinh
  acosh = interp__'app interp__acosh
  atanh = interp__'app interp__atanh


----------------------------------------------------------------------
-- * Interpreting Probability Expressions
----------------------------------------------------------------------

-- | Convert a real to a probability
realToProb :: R -> Prob
realToProb r | r < 0 = 0
realToProb r = Prob $ Log.Exp $ log r

-- | Convert a real in log space to a probability
logRealToProb :: R -> Prob
logRealToProb = Prob . Log.Exp

-- | Convert a probability to a real
probToReal :: Prob -> R
probToReal = exp . Log.ln . fromProb

-- | Convert a probability to a real in log space
probToLogReal :: Prob -> R
probToLogReal = Log.ln . fromProb

class ValidExprRepr repr => Interp__realToProb repr where
  interp__realToProb :: GExpr repr (R -> Prob)

class ValidExprRepr repr => Interp__logRealToProb repr where
  interp__logRealToProb :: GExpr repr (R -> Prob)

class ValidExprRepr repr => Interp__probToReal repr where
  interp__probToReal :: GExpr repr (Prob -> R)

class ValidExprRepr repr => Interp__probToLogReal repr where
  interp__probToLogReal :: GExpr repr (Prob -> R)

-- | Compute the log-gamma function as a map from reals to probabilities
gammaProb :: R -> Prob
gammaProb = Prob . Log.Exp . logGamma

class ValidExprRepr repr => Interp__gammaProb repr where
  interp__gammaProb :: GExpr repr (R -> Prob)

class ValidExprRepr repr => Interp__digamma repr where
  interp__digamma :: GExpr repr (R -> R)

instance (Interp__gammaProb repr, Interp__probToLogReal repr,
          Interp__digamma repr) =>
         HasGamma (GExpr repr R) where
  logGamma =
    interp__'app interp__probToLogReal .
    interp__'app interp__gammaProb
  digamma = interp__'app interp__digamma


----------------------------------------------------------------------
-- * Interpreting Distributions
----------------------------------------------------------------------

class ValidExprRepr repr => Interp__delta repr a where
  interp__delta :: GExpr repr (a -> Dist a)

class ValidExprRepr repr => Interp__normal repr where
  interp__normal :: GExpr repr (R -> R -> Dist R)

class ValidExprRepr repr => Interp__uniform repr where
  interp__uniform :: GExpr repr (R -> R -> Dist R)

class ValidExprRepr repr => Interp__exponential repr where
  interp__exponential :: GExpr repr (R -> Dist R)

class ValidExprRepr repr => Interp__gamma repr where
  interp__gamma :: GExpr repr (R -> R -> Dist R)

class ValidExprRepr repr => Interp__beta repr where
  interp__beta :: GExpr repr (R -> R -> Dist R)

class ValidExprRepr repr => Interp__betaProb repr where
  interp__betaProb :: GExpr repr (R -> R -> Dist Prob)

class ValidExprRepr repr => Interp__iidV repr where
  interp__iidV :: GExpr repr (Int -> Dist R -> Dist RVector)

class ValidExprRepr repr => Interp__iidPV repr where
  interp__iidPV :: GExpr repr (Int -> Dist Prob -> Dist ProbVector)

class ValidExprRepr repr => Interp__dirichlet repr where
  interp__dirichlet :: GExpr repr (GList R -> Dist (GList R))

class ValidExprRepr repr => Interp__dirichletProb repr where
  interp__dirichletProb :: GExpr repr (GList R -> Dist (GList Prob))

class ValidExprRepr repr => Interp__dirichletV repr where
  interp__dirichletV :: GExpr repr (RVector -> Dist RVector)

class ValidExprRepr repr => Interp__dirichletPV repr where
  interp__dirichletPV :: GExpr repr (RVector -> Dist ProbVector)

class ValidExprRepr repr => Interp__categorical repr where
  interp__categorical :: GExpr repr (GList Prob -> Dist Int)

class ValidExprRepr repr => Interp__poisson repr where
  interp__poisson :: GExpr repr (R -> Dist Int)

class ValidExprRepr repr => Interp__binary_mixture repr a where
  interp__binary_mixture :: GExpr repr (Prob -> Dist a -> Dist a -> Dist a)

class ValidExprRepr repr => Interp__scaleDist repr a where
  interp__scaleDist :: GExpr repr (Prob -> Dist a -> Dist a)

class ValidExprRepr repr => Interp__ctorDist__ListF repr where
  interp__ctorDist__Nil ::
    GExpr repr (Dist (GTuple '[]) -> Dist (GList a))
  interp__ctorDist__Cons ::
    GExpr repr (Dist (GTuple '[a, GList a]) -> Dist (GList a))

class ValidExprRepr repr => Interp__adtDist__ListF repr where
  interp__adtDist__ListF :: GExpr repr
    (Prob -> Dist (GTuple '[]) -> Prob -> Dist (GTuple '[a, GList a]) ->
     Dist (GList a))

class ValidExprRepr repr => Interp__list_iid repr where
  interp__list_iid :: GExpr repr (Dist a -> Dist (GList a))


-- | This is the reference measure on a set, i.e., the Lebesgue measure on the
-- reals and the counting measure on any discrete set like the integers. This
-- measure represents a distribution that chooses an arbitrary element of the
-- type. Note that this is generally an improper probability distribution, i.e.,
-- the probability of each element is 1, with infinite total probability.
class ValidExprRepr repr => Interp__arbitrary repr a where
  interp__arbitrary :: GExpr repr (Dist a)


----------------------------------------------------------------------
-- * Interpreting general vectors
----------------------------------------------------------------------

class ValidExprRepr repr => Interp__vec_iid repr a where
  interp__vec_iid :: GExpr repr (Int -> Dist a -> Dist (Vector a))

-- | Build a distribution on 'Vector's from one on lists
class ValidExprRepr repr => Interp__vec_dist repr a where
  interp__vec_dist :: GExpr repr (Dist (GList a) -> Dist (Vector a))

class ValidExprRepr repr => Interp__vec_nil_dist repr a where
  interp__vec_nil_dist :: GExpr repr (Dist (Vector a))

class ValidExprRepr repr => Interp__vec_cons_dist repr a where
  interp__vec_cons_dist :: GExpr repr (Dist (GTuple '[a, Vector a]) ->
                                       Dist (Vector a))

class ValidExprRepr repr => Interp__vec_head repr a where
  interp__vec_head :: GExpr repr (Vector a -> a)

class ValidExprRepr repr => Interp__vec_tail repr a where
  interp__vec_tail :: GExpr repr (Vector a -> Vector a)

class ValidExprRepr repr => Interp__vec_nth repr a where
  interp__vec_nth :: GExpr repr (Vector a -> Int -> a)

class ValidExprRepr repr => Interp__vec_length repr a where
  interp__vec_length :: GExpr repr (Vector a -> Int)

class ValidExprRepr repr => Interp__vec_generate repr a where
  interp__vec_generate :: GExpr repr (Int -> (Int -> a) -> Vector a)

class ValidExprRepr repr => Interp__vec_map repr a b where
  interp__vec_map :: GExpr repr ((a -> b) -> Vector a -> Vector b)

class ValidExprRepr repr => Interp__vec_foldr repr a b where
  interp__vec_foldr :: GExpr repr ((a -> b -> b) -> b -> Vector a -> b)


----------------------------------------------------------------------
-- * Interpreting unboxed vectors and matrices
----------------------------------------------------------------------

class ValidExprRepr repr => Interp__lengthV repr where
  interp__lengthV :: GExpr repr (RVector -> Int)

class ValidExprRepr repr => Interp__atV repr where
  interp__atV :: GExpr repr (RVector -> Int -> R)

class ValidExprRepr repr => Interp__mapV repr where
  interp__mapV :: GExpr repr ((R -> R) -> RVector -> RVector)

class ValidExprRepr repr => Interp__foldrV repr where
  interp__foldrV :: GExpr repr ((R -> b -> b) -> b -> RVector -> b)

class ValidExprRepr repr => Interp__sumV repr where
  interp__sumV :: GExpr repr (RVector -> R)

class ValidExprRepr repr => Interp__generateV repr where
  interp__generateV :: GExpr repr (Int -> (Int -> R) -> RVector)

class ValidExprRepr repr => Interp__boxV repr where
  interp__boxV :: GExpr repr (Vector R -> RVector)

class ValidExprRepr repr => Interp__unboxV repr where
  interp__unboxV :: GExpr repr (RVector -> Vector R)

class ValidExprRepr repr => Interp__rowsM repr where
  interp__rowsM :: GExpr repr (RMatrix -> Int)

class ValidExprRepr repr => Interp__colsM repr where
  interp__colsM :: GExpr repr (RMatrix -> Int)

class ValidExprRepr repr => Interp__atM repr where
  interp__atM :: GExpr repr (RMatrix -> Int -> Int -> R)

class ValidExprRepr repr => Interp__fromRowsM repr where
  interp__fromRowsM :: GExpr repr (GList RVector -> RMatrix)

class ValidExprRepr repr => Interp__fromColsM repr where
  interp__fromColsM :: GExpr repr (GList RVector -> RMatrix)

class ValidExprRepr repr => Interp__toRowsM repr where
  interp__toRowsM :: GExpr repr (RMatrix -> GList RVector)

class ValidExprRepr repr => Interp__toColsM repr where
  interp__toColsM :: GExpr repr (RMatrix -> GList RVector)

class ValidExprRepr repr => Interp__mulM repr where
  interp__mulM :: GExpr repr (RMatrix -> RMatrix -> RMatrix)

class ValidExprRepr repr => Interp__mulMV repr where
  interp__mulMV :: GExpr repr (RMatrix -> RVector -> RVector)

class ValidExprRepr repr => Interp__mulVM repr where
  interp__mulVM :: GExpr repr (RVector -> RMatrix -> RVector)


----------------------------------------------------------------------
-- * Interpreting unboxed vectors and matrices of probabilities
----------------------------------------------------------------------

class ValidExprRepr repr => Interp__lengthPV repr where
  interp__lengthPV :: GExpr repr (ProbVector -> Int)

class ValidExprRepr repr => Interp__atPV repr where
  interp__atPV :: GExpr repr (ProbVector -> Int -> Prob)

class ValidExprRepr repr => Interp__generatePV repr where
  interp__generatePV :: GExpr repr (Int -> (Int -> Prob) -> ProbVector)

class ValidExprRepr repr => Interp__boxPV repr where
  interp__boxPV :: GExpr repr (Vector Prob -> ProbVector)

class ValidExprRepr repr => Interp__unboxPV repr where
  interp__unboxPV :: GExpr repr (ProbVector -> Vector Prob)

class ValidExprRepr repr => Interp__mapPV repr where
  interp__mapPV :: GExpr repr ((Prob -> Prob) -> ProbVector -> ProbVector)

class ValidExprRepr repr => Interp__foldrPV repr where
  interp__foldrPV :: GExpr repr ((Prob -> b -> b) -> b -> ProbVector -> b)

class ValidExprRepr repr => Interp__sumPV repr where
  interp__sumPV :: GExpr repr (ProbVector -> Prob)

class ValidExprRepr repr => Interp__rowsPM repr where
  interp__rowsPM :: GExpr repr (ProbMatrix -> Int)

class ValidExprRepr repr => Interp__colsPM repr where
  interp__colsPM :: GExpr repr (ProbMatrix -> Int)

class ValidExprRepr repr => Interp__atPM repr where
  interp__atPM :: GExpr repr (ProbMatrix -> Int -> Int -> Prob)

class ValidExprRepr repr => Interp__fromRowsPM repr where
  interp__fromRowsPM :: GExpr repr (GList ProbVector -> ProbMatrix)

class ValidExprRepr repr => Interp__fromColsPM repr where
  interp__fromColsPM :: GExpr repr (GList ProbVector -> ProbMatrix)

class ValidExprRepr repr => Interp__toRowsPM repr where
  interp__toRowsPM :: GExpr repr (ProbMatrix -> GList ProbVector)

class ValidExprRepr repr => Interp__toColsPM repr where
  interp__toColsPM :: GExpr repr (ProbMatrix -> GList ProbVector)

class ValidExprRepr repr => Interp__mulPM repr where
  interp__mulPM :: GExpr repr (ProbMatrix -> ProbMatrix -> ProbMatrix)

class ValidExprRepr repr => Interp__mulPMV repr where
  interp__mulPMV :: GExpr repr (ProbMatrix -> ProbVector -> ProbVector)

class ValidExprRepr repr => Interp__mulPVM repr where
  interp__mulPVM :: GExpr repr (ProbVector -> ProbMatrix -> ProbVector)


----------------------------------------------------------------------
-- * Distributions involving unboxed vectors and matrices of probabilities
----------------------------------------------------------------------

class ValidExprRepr repr => Interp__categoricalV repr where
  interp__categoricalV :: GExpr repr (RVector -> Dist Int)

class ValidExprRepr repr => Interp__categoricalPV repr where
  interp__categoricalPV :: GExpr repr (ProbVector -> Dist Int)

class ValidExprRepr repr => Interp__mv_normal repr where
  interp__mvNormal :: GExpr repr (RMatrix -> RMatrix -> Dist RMatrix)


----------------------------------------------------------------------
-- * Misc
----------------------------------------------------------------------

-- | Like the Haskell 'error' function, but takes a numeric id (so we do not
-- have to parse strings)
gerror :: Int -> a
gerror i = error $ "Error number " ++ show i ++ " in Grappa model"

-- | Typeclass for interpreting 'gerror'
class ValidExprRepr repr => Interp__gerror repr a where
  interp__gerror :: GExpr repr (Int -> a)

-- | Like the Haskell 'trace' function, but takes a numeric id (so we do not
-- have to parse strings)
gtrace :: Show a => Int -> a -> b -> b
gtrace i a b = trace ("gtrace " ++ show i ++ ": " ++ show a) b

-- | Typeclass for interpreting 'gtrace'
class (ValidExprRepr repr, Show a) => Interp__gtrace repr a b where
  interp__gtrace :: GExpr repr (Int -> a -> b -> b)


----------------------------------------------------------------------
-- * Typeclasses for Interpreting Distribution Families in Grappa
----------------------------------------------------------------------

-- | The Grappa type of size expressions used in VI distribution families
data VISize

instance GrappaType VISize where
  grappaTypeRepr = GrappaBaseType GrappaTypeAppBase

instance Num VISize where
  sz + _ = sz
  sz - _ = sz
  sz * _ = sz
  abs sz = sz
  signum sz = sz
  fromInteger _ = error "fromInteger: VISize"

-- | The Grappa type of VI distribution families
data VIDist a

class ValidExprRepr repr => Interp__withVISize repr where
  interp__withVISize :: GExpr repr ((VISize -> VIDist a) -> VIDist a)

class ValidExprRepr repr => Interp__viNormal repr where
  interp__viNormal :: GExpr repr (VIDist Double)

class ValidExprRepr repr => Interp__viUniform repr where
  interp__viUniform :: GExpr repr (VIDist Double)

class ValidExprRepr repr => Interp__viGamma repr where
  interp__viGamma :: GExpr repr (VIDist Double)

class ValidExprRepr repr => Interp__viGammaProb repr where
  interp__viGammaProb :: GExpr repr (VIDist Prob)

class ValidExprRepr repr => Interp__viBeta repr where
  interp__viBeta :: GExpr repr (VIDist Double)

class ValidExprRepr repr => Interp__viBetaProb repr where
  interp__viBetaProb :: GExpr repr (VIDist Prob)

class ValidExprRepr repr => Interp__viDelta repr a where
  interp__viDelta :: GExpr repr (a -> VIDist a)

class ValidExprRepr repr => Interp__viCategorical repr where
  interp__viCategorical :: GExpr repr (VISize -> VIDist Int)

class ValidExprRepr repr => Interp__viDirichlet repr where
  interp__viDirichlet :: GExpr repr (VISize -> VIDist (GList R))

class ValidExprRepr repr => Interp__viDirichletProb repr where
  interp__viDirichletProb :: GExpr repr (VISize -> VIDist (GList Prob))

class ValidExprRepr repr => Interp__viDirichletV repr where
  interp__viDirichletV :: GExpr repr (VISize -> VIDist RVector)

class ValidExprRepr repr => Interp__viDirichletPV repr where
  interp__viDirichletPV :: GExpr repr (VISize -> VIDist ProbVector)

class ValidExprRepr repr => Interp__viTuple0 repr where
  interp__viTuple0 :: GExpr repr (VIDist (GTuple '[]))

class ValidExprRepr repr => Interp__viTuple1 repr a where
  interp__viTuple1 :: GExpr repr (VIDist a -> VIDist (GTuple '[a]))

class ValidExprRepr repr => Interp__viTuple2 repr a b where
  interp__viTuple2 :: GExpr repr (VIDist a -> VIDist b ->
                                  VIDist (GTuple '[a, b]))

class ValidExprRepr repr => Interp__viTuple3 repr a b c where
  interp__viTuple3 :: GExpr repr (VIDist a -> VIDist b -> VIDist c ->
                                  VIDist (GTuple '[a, b, c]))

class ValidExprRepr repr => Interp__viTuple4 repr a b c d where
  interp__viTuple4 :: GExpr repr (VIDist a -> VIDist b -> VIDist c ->
                                  VIDist d -> VIDist (GTuple '[a, b, c, d]))

class ValidExprRepr repr => Interp__viIID repr a where
  interp__viIID :: GExpr repr (VISize -> VIDist a -> VIDist (GList a))

class ValidExprRepr repr => Interp__viVecDist repr a where
  interp__viVecDist :: GExpr repr (Vector (VIDist a) -> VIDist (Vector a))

class ValidExprRepr repr => Interp__viVecIID repr a where
  interp__viVecIID :: GExpr repr (VISize -> VIDist a -> VIDist (Vector a))

class ValidExprRepr repr => Interp__viIIDV repr where
  interp__viIIDV :: GExpr repr (VISize -> VIDist R -> VIDist RVector)

class ValidExprRepr repr => Interp__viIIDPV repr where
  interp__viIIDPV :: GExpr repr (VISize -> VIDist Prob -> VIDist ProbVector)

class ValidExprRepr repr => Interp__viJSONInput repr a where
  interp__viJSONInput :: GExpr repr (VIDist a)

class ValidExprRepr repr => Interp__viMappedJSONInput repr a b where
  interp__viMappedJSONInput :: GExpr repr ((a -> VIDist b) -> VIDist b)


----------------------------------------------------------------------
-- * Example Models
----------------------------------------------------------------------

-- A completely empty model, like
-- model { } = nothing
emptyModel :: ValidRepr repr => GExpr repr (Dist (GTuple '[]))
emptyModel = interp__'mkDist $ \ v ->
  interp__'vProjTuple v
    (\ Tuple0 -> interp__'return (interp__'injTuple Tuple0))

-- A model that samples from a normal, like
-- model { x } = x ~ normal 0 1
basicModel :: ( ValidRepr repr
              , Interp__normal repr
              , Interp__'integer repr R
              ) => GExpr repr (Dist R)
basicModel = interp__'mkDist $ \ vx ->
  interp__'sample (interp__normal `interp__'app` (interp__'integer 0)
                                  `interp__'app` (interp__'integer 1))
                  vx $ \x -> interp__'return x

-- A model that samples from a normal, like
-- model d { x } = x ~ d
distParamModel :: (ValidRepr repr, Interp__normal repr) =>
                  GExpr repr (Dist R -> Dist R)
distParamModel = interp__'lam $ \ d ->
  interp__'mkDist $ \ vx ->
  interp__'sample d vx $ \x -> interp__'return x

-- A model that samples from a normal, like
-- model { x, y } = x ~ normal 0 1; y ~ normal 0 1
twoVarModel :: (ValidRepr repr, Interp__normal repr, Interp__'integer repr R) =>
               GExpr repr (Dist (GTuple '[R,R]))
twoVarModel = interp__'mkDist $ \ vs ->
  interp__'vProjTuple vs
    (\ (Tuple2 vx vy) ->
      interp__'sample (interp__normal `interp__'app` (interp__'integer 0)
                                      `interp__'app` (interp__'integer 1)) vx $
        \x -> interp__'sample (interp__normal `interp__'app` (interp__'integer 0)
                                      `interp__'app` (interp__'integer 1)) vy $
        \y -> interp__'return (interp__'injTuple (Tuple2 x y)))

-- A model that samples from a normal, like
-- model { x, y } = x ~ normal 0 1; y ~ normal 0 1
tupleArgModel :: ( ValidRepr repr, Interp__normal repr) =>
                 GExpr repr (GTuple '[R,R] -> Dist R)
tupleArgModel = interp__'lam $ \ vtup ->
  interp__'projTuple vtup (\ (Tuple2 x y) ->
    interp__'mkDist $ \ v ->
    interp__'sample (interp__normal `interp__'app` x `interp__'app` y) v interp__'return)

-- A model that loops over a list, like
-- model m { Nil } = empty
lNil :: (ValidRepr repr, Interp__ctorDist__ListF repr) =>
        GExpr repr (Dist (GList R))
lNil = interp__'mkDist $ \ v ->
  let nDist = interp__'mkDist $ \_ -> interp__'return (interp__'injTuple Tuple0)
  in interp__'sample (interp__ctorDist__Nil `interp__'app` nDist) v interp__'return

-- A list model, like
-- model m { Nil       | 0.5 } = empty
--         { Cons x xs | 0.5 } = x ~ normal 0 1; xs ~ m
listModel :: ( ValidRepr repr
             , Interp__'integer repr R
             , Interp__normal repr
             , Interp__'rational repr Prob
             , Interp__adtDist__ListF repr
             ) => GExpr repr (Dist (GList R))
listModel = interp__'mkDist $ \ v ->
  let dist = interp__adtDist__ListF `interp__'app`
               (interp__'rational 0.5) `interp__'app`
               nDist  `interp__'app`
               (interp__'rational 0.5)  `interp__'app`
               cDist
      cDist = interp__'mkDist $ \ tup ->
        interp__'vProjTuple tup $ \ (Tuple2 vx vxs) ->
        interp__'sample (interp__normal `interp__'app` (interp__'integer 0)
                               `interp__'app` (interp__'integer 1)) vx $ \ x ->
        interp__'sample listModel vxs $ \xs ->
        interp__'return (interp__'injTuple (Tuple2 x xs))
      nDist = interp__'mkDist $ \ _ ->
        interp__'return (interp__'injTuple Tuple0)
  in interp__'sample dist v interp__'return

interp__empty2 ::
      forall repr a_a4bMy.
      (ValidRepr repr, Interp__'integer repr a_a4bMy,
       Interp__'plus repr a_a4bMy) =>
      GExpr repr a_a4bMy -> GExpr repr (Dist (GTuple '[]))
interp__empty2 x
      = interp__'mkDist
          (\ tup -> interp__'vProjTuple tup $ \ Tuple0 ->
             let y = interp__'integer 5 in
             let _ = interp__'app (interp__'app interp__'plus x) y
             in interp__'return (interp__'injTuple Tuple0))

{-
interp__sum ::
  forall repr.
  ( Interp__'integer repr Int
  , Interp__'plus repr Int
  , Interp__ADT repr (ListF Int)
  ) => GExpr repr (GList Int -> Int)
interp__sum = interp__'lam $ \ lst ->
  interp__'projADT lst $ \ __s ->
    case __s of
      Cons x xs -> interp__'app (interp__'app interp__'plus x) (interp__'app interp__sum xs)
      Nil       -> interp__'integer 0
-}


----------------------------------------------------------------------
-- * Embedding Haskell Data into Representations
----------------------------------------------------------------------

-- | Typeclass stating that Haskell data of type @a@ can be embedded into Grappa
-- representation @repr@
class EmbedRepr repr a where
  embedRepr :: a -> GExpr repr a
