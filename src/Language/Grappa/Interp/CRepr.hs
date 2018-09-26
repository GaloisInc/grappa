{-# LANGUAGE TypeFamilies, GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Language.Grappa.Interp.CRepr where

import           Control.Monad.State
import           Data.Type.Equality
import qualified Numeric.Log as Log

import           Language.Grappa.Distribution
import           Language.Grappa.Interp
import           Language.Grappa.GrappaInternals
import           Language.Grappa.Interp.CExpr


-- | The type tag for the C representation.
data CRepr

-- | A variable is a de Bruijn level integer along with its type.
type CVar a = (CType a, Int)

-- | Partially static representation for C expressions. Dynamic
-- expressions are injected via the CExprDynamic and CExprDynamicProb
-- constructors, and the rest are for static expressions.
data CExpr a where
  CExprDynamic :: CDynExpr a -> CExpr a
  CExprDynamicProb :: Log.Log (CDynExpr R) -> CExpr Prob

  CExprBool   :: Bool -> CExpr Bool
  CExprInt    :: Int -> CExpr Int
  CExprDouble :: R -> CExpr R
  CExprProb   :: Prob -> CExpr Prob

  CExprFun   :: (CExpr a -> CExpr b) -> CExpr (a -> b)
  CExprTuple :: TupleF ts CExpr (ADT (TupleF ts)) ->
                 CExpr (ADT (TupleF ts))
  CExprDist ::
    (CVar a -> State Int (CDist a)) -> CExpr (Dist a)

-- | Project out the dynamic expression or convert to one if possible.
toCDynExpr :: CExpr a -> CDynExpr a
toCDynExpr (CExprDynamic e) = e
toCDynExpr (CExprBool b)    = LitExpr BoolType $ BoolLit b
toCDynExpr (CExprInt i)     = LitExpr IntType $ IntLit i
toCDynExpr (CExprDouble d)  = LitExpr DoubleType $ DoubleLit d
toCDynExpr _ = error "toCDynExpr: unexpected CExpr"

-- | Get the CType associated with a CExpr
cExprType :: CExpr a -> CType a
cExprType (CExprDynamic e) = cDynExprType e
cExprType (CExprBool _)    = BoolType
cExprType (CExprInt _)     = IntType
cExprType (CExprDouble _)  = DoubleType
cExprType (CExprTuple tup) =
  TupleType $ mapHList cExprType $ tupleToHList tup
cExprType _ = error "cExprType: unsupported CExpr"


-- These are not needed for now since we're just using hand-written C
-- functions for uniform, normal, etc. distributions.

-- cExprRealToProb :: CExpr R -> CExpr Prob
-- cExprRealToProb (CExprDouble d)  = CExprProb $ realToProb d
-- cExprRealToProb (CExprDynamic e) =
--   CExprDynamicProb $ Log.Exp $ cDynFunCall "log" e

-- cExprLogRealToProb :: CExpr R -> CExpr Prob
-- cExprLogRealToProb (CExprDouble d)  = CExprProb $ logRealToProb d
-- cExprLogRealToProb (CExprDynamic e) = CExprDynamicProb $ Log.Exp e

-- cExprProbToReal :: CExpr Prob -> CExpr R
-- cExprProbToReal (CExprProb p)        = CExprDouble $ probToReal p
-- cExprProbToReal (CExprDynamicProb e) =
--   CExprDynamic $ cDynFunCall "exp" $ Log.ln e
-- cExprProbToReal (CExprDynamic _)     =
--   error "cExprProbToReal: unexpected CExprDynamic"

-- cExprProbToLogReal :: CExpr Prob -> CExpr R
-- cExprProbToLogReal (CExprProb p)        = CExprDouble $ probToLogReal p
-- cExprProbToLogReal (CExprDynamicProb e) = CExprDynamic $ Log.ln e
-- cExprProbToLogReal (CExprDynamic _)     =
--   error "cExprProbToLogReal: unexpected CExprDynamic"


-- | Projections for functions, tuples, and dists. 

projCFun :: CExpr (a -> b) -> CExpr a -> CExpr b
projCFun (CExprDynamic _) = error "projCFun: unexpected CExprDynamic"
projCFun (CExprFun f)     = f

projCTuple :: CExpr (ADT (TupleF ts)) ->
              TupleF ts (GExpr CRepr) (ADT (TupleF ts))
projCTuple (CExprDynamic e) =
  case cDynExprType e of
    TupleType ts ->
      hListToTuple $ mapHList
      (\elemPf -> GExpr $ CExprDynamic $ TupleProjExpr ts elemPf e)
      (buildHListElems ts)
projCTuple (CExprTuple tup) = mapADT GExpr tup

projCDist :: CExpr (Dist a) -> CVar a -> State Int (CDist a)
projCDist (CExprDynamic _) = error "projCDist: unexpected dynamic"
projCDist (CExprDist d)    = d

projCInt :: CExpr Int -> Int
projCInt (CExprDynamic _) = error "projCDist: unexpected dynamic"
projCInt (CExprInt i)     = i


-- | Create CExprs from integers or rationals.

cExprFromInteger :: (Num a) => CType a -> Integer -> CExpr a
cExprFromInteger DoubleType = CExprDouble . fromInteger
cExprFromInteger IntType    = CExprInt . fromInteger
cExprFromInteger BoolType   = CExprBool . fromInteger
cExprFromInteger _ = error "cExprFromInteger: unsupported type"

cExprFromRational :: (Fractional a) => CType a -> Rational -> CExpr a
cExprFromRational DoubleType = CExprDouble . fromRational
cExprFromRational IntType    = CExprInt . fromRational
cExprFromRational BoolType   = CExprBool . fromRational
cExprFromRational _ = error "cExprFromRational: unsupported type"


-- | Injection of values of base types into CExpr.

instance EmbedRepr CRepr Bool where embedRepr = GExpr . CExprBool
instance EmbedRepr CRepr Int where embedRepr  = GExpr . CExprInt
instance EmbedRepr CRepr R where embedRepr    = GExpr . CExprDouble
instance EmbedRepr CRepr Prob where embedRepr = GExpr . CExprProb


-- | Representation of expressions.
instance ValidExprRepr CRepr where
  type GExprRepr CRepr a = CExpr a
  interp__'bottom = error "CRepr: unexpected bottom!"

  interp__'injTuple tup = GExpr $ CExprTuple $ mapADT unGExpr tup
  interp__'projTuple (GExpr tup) k = k (projCTuple tup)

  interp__'app (GExpr f) (GExpr x) = GExpr $ (projCFun f) x
  interp__'lam f = GExpr $ CExprFun $ unGExpr . f . GExpr
  interp__'fix f = f (interp__'fix f)


-- | With strong tuples.
instance StrongTupleRepr CRepr where
  interp__'strongProjTuple (GExpr tup) = projCTuple tup


-- | Representation of programs.
instance ValidRepr CRepr where
  type GVExprRepr CRepr a = CVar a
  type GStmtRepr CRepr a  = State Int [SomeCDist]

  interp__'projTupleStmt (GExpr tup) k = k $ projCTuple tup
  interp__'vInjTuple _ = error "CRepr: unexpected vInjTuple"
  interp__'vProjTuple (GVExpr (TupleType ts, ve)) k = GStmt $ do
    next_var <- get
    if ve == next_var then return () else
      error $ "vProjTuple: wrong variable number: expected '" ++
      show next_var ++ "' but got '" ++ show ve ++ "'."
    -- Starting from the current var #, associate with each type in ts
    -- a var #, yielding a list of (type, var #) pairs.
    vexprs <- traverseHList (\ty -> do
                                  i <- get
                                  modify (+1)
                                  return $ GVExpr (ty, i)) ts
    put next_var -- reset the state
    unGStmt $ k $ hListToTuple vexprs

  interp__'vwild _   = error "CRepr: unexpected wild"
  interp__'vlift _ _ = error "CRepr: unexpected lift"

  interp__'return _ = GStmt $ return []
  interp__'let rhs body = body rhs

  interp__'sample (GExpr d) (GVExpr (tp, v)) k = GStmt $ do
    cur_var <- get
    if v /= cur_var then error "variable out of order" else do
      dist <- projCDist d (tp, v)
      put (cur_var + 1)
      dists <- unGStmt $ k (GExpr $ CExprDynamic $
                            VarExpr (cDistType dist) $ VarName v)
      return (SomeCDist dist : dists)

  interp__'mkDist f =
    GExpr $ CExprDist $ \v@(tp, _) ->
    coerceStmtRet tp . tupleCDist <$> unGStmt (f (GVExpr v))


-- | Coerce an existentially typed SomeCDist to a CDist a, checking
-- that the types match at runtime.
coerceStmtRet :: CType a -> SomeCDist -> CDist a
coerceStmtRet DoubleType (SomeCDist (DoubleDist d)) = DoubleDist d
coerceStmtRet IntType (SomeCDist (IntDist d))       = IntDist d
coerceStmtRet BoolType (SomeCDist (BoolDist d))     = BoolDist d
coerceStmtRet t d =
  case d of
    SomeCDist d' ->
      case cTypeEq t (cDistType d') of
        Just Refl -> d'
        Nothing ->
          error $ "coerceStmtRet: type mismatch: expected '" ++
          show t ++ "' but found '" ++ show (cDistType d') ++ "'."


-- | Helpers for instances of unary and binary expression classes.

unaryExpr :: EmbedRepr CRepr b => (a -> b) ->
             GExpr CRepr (a -> b) -> GExpr CRepr a -> GExpr CRepr b
unaryExpr fstatic _ (GExpr (CExprBool b))   = embedRepr $ fstatic b
unaryExpr fstatic _ (GExpr (CExprInt i))    = embedRepr $ fstatic i
unaryExpr fstatic _ (GExpr (CExprDouble d)) = embedRepr $ fstatic d
unaryExpr fstatic _ (GExpr (CExprProb p))   = embedRepr $ fstatic p
unaryExpr _ fdyn e = interp__'app fdyn e

unaryCExpr :: EmbedRepr CRepr b => (a -> b) -> GExpr CRepr (a -> b) ->
              GExpr CRepr (a -> b)
unaryCExpr fstatic fdyn =
  interp__'lam $ unaryExpr fstatic fdyn

unaryCExprOp :: EmbedRepr CRepr a => (a -> a) ->
                UnaryOp -> GExpr CRepr (a -> a)
unaryCExprOp fstatic op =
  unaryCExpr fstatic
  (GExpr $ CExprFun $ \x -> CExprDynamic $ UnaryExpr op (toCDynExpr x))

unaryCExprFun :: EmbedRepr CRepr b => (a -> b) ->
                 (CExpr a -> CExpr b) -> GExpr CRepr (a -> b)
unaryCExprFun fstatic f =
  unaryCExpr fstatic $ GExpr $ CExprFun f

binaryExpr :: EmbedRepr CRepr c => (a -> b -> c) ->
              GExpr CRepr (a -> b -> c) -> GExpr CRepr a ->
              GExpr CRepr b -> GExpr CRepr c
binaryExpr fstatic _ (GExpr (CExprBool b1)) (GExpr (CExprBool b2)) =
  embedRepr $ fstatic b1 b2
binaryExpr fstatic _ (GExpr (CExprInt i1)) (GExpr (CExprInt i2)) =
  embedRepr $ fstatic i1 i2
binaryExpr fstatic _ (GExpr (CExprDouble d1)) (GExpr (CExprDouble d2)) =
  embedRepr $ fstatic d1 d2
binaryExpr fstatic _ (GExpr (CExprProb p1)) (GExpr (CExprProb p2)) =
  embedRepr $ fstatic p1 p2
binaryExpr _ fdyn e1 e2 = interp__'app (interp__'app fdyn e1) e2

binaryCExpr :: EmbedRepr CRepr b => (a -> a -> b) ->
               GExpr CRepr (a -> a -> b) -> GExpr CRepr (a -> a -> b)
binaryCExpr fstatic fdyn =
  interp__'lam $ interp__'lam . binaryExpr fstatic fdyn

binaryCExprOp :: (HasCType b, EmbedRepr CRepr b) => (a -> a -> b) ->
                 BinaryOp -> GExpr CRepr (a -> a -> b)
binaryCExprOp fstatic op =
  binaryCExpr fstatic
  (GExpr $ CExprFun $ \x -> CExprFun $ \y -> CExprDynamic $
    BinaryExpr cType op (toCDynExpr x) (toCDynExpr y))


-- | Boolean expressions

instance Interp__'ifThenElse CRepr where
  interp__'ifThenElse (GExpr (CExprBool b)) e1 e2 =
    if b then e1 else e2
  interp__'ifThenElse (GExpr b) (GExpr e1) (GExpr e2) =
    GExpr $ CExprDynamic $
    CondExpr (toCDynExpr b) (toCDynExpr e1) (toCDynExpr e2)
    -- TODO: ^ can e1 and e2 be reduced more?

instance Interp__not CRepr where
  interp__not = unaryCExprOp not NotOp


-- | Comparison expressions

instance Eq a => Interp__'eq'eq CRepr a where
  interp__'eq'eq = binaryCExprOp (==) EqOp

instance Ord a => Interp__'lt CRepr a where
  interp__'lt = binaryCExprOp (<) LtOp

instance Ord a => Interp__'gt CRepr a where
  interp__'gt = binaryCExprOp (>) GtOp

instance Ord a => Interp__'lt'eq CRepr a where
  interp__'lt'eq = binaryCExprOp (<=) LteOp

instance Ord a => Interp__'gt'eq CRepr a where
  interp__'gt'eq = binaryCExprOp (>=) GteOp

instance (Ord a, EmbedRepr CRepr a) =>
  Interp__min CRepr a where
  interp__min =
    binaryCExpr min $ interp__'lam $ \x -> interp__'lam $ \y ->
    interp__'ifThenElse (interp__'app (interp__'app interp__'lt'eq x) y) x y

instance (Ord a, EmbedRepr CRepr a) =>
  Interp__max CRepr a where
  interp__max =
    binaryCExpr max $ interp__'lam $ \x -> interp__'lam $ \y ->
    interp__'ifThenElse (interp__'app (interp__'app interp__'gt'eq x) y) x y


-- | Numeric expressions

instance (Num a, HasCType a, EmbedRepr CRepr a) =>
  Interp__'plus CRepr a where
  interp__'plus = binaryCExprOp (+) PlusOp

instance (Num a, HasCType a, EmbedRepr CRepr a) =>
  Interp__'minus CRepr a where
  interp__'minus = binaryCExprOp (-) MinusOp

instance (Num a, HasCType a, EmbedRepr CRepr a) =>
  Interp__'times CRepr a where
  interp__'times = binaryCExprOp (*) TimesOp

instance (Num a, EmbedRepr CRepr a) =>
  Interp__negate CRepr a where
  interp__negate = unaryCExprOp negate NegateOp

instance (Num a, Ord a, EmbedRepr CRepr a) =>
  Interp__abs CRepr a where
  interp__abs = unaryCExpr abs $
    interp__'lam $ \x -> interp__'app (interp__'app interp__max x)
                         (interp__'app interp__negate x)

instance (Num a, Ord a, HasCType a, EmbedRepr CRepr a) =>
  Interp__signum CRepr a where
  interp__signum = unaryCExpr signum $ interp__'lam $
    \x -> ite x interp__'gt one (ite x interp__'lt neg_one zero)
    where
      one = (GExpr $ CExprDynamic $ cDynOne cType)
      zero = (GExpr $ CExprDynamic $ cDynZero cType)
      neg_one = interp__'app interp__negate one
      ite x comp tru fls =
        interp__'ifThenElse (interp__'app (interp__'app comp x)
                              (GExpr $ CExprDynamic $ cDynZero cType))
        tru fls

instance (Num a, HasCType a) => Interp__'integer CRepr a where
  interp__'integer = GExpr . cExprFromInteger cType

instance (Fractional a, HasCType a, EmbedRepr CRepr a) =>
  Interp__'div CRepr a where
  interp__'div = binaryCExprOp (/) DivOp

instance (Fractional a, HasCType a, EmbedRepr CRepr a) =>
  Interp__recip CRepr a where
  interp__recip = unaryCExpr recip $
    interp__'app interp__'div (GExpr $ CExprDynamic $ cDynOne $ cType)

instance (Fractional a, HasCType a) => Interp__'rational CRepr a where
  interp__'rational = GExpr . cExprFromRational cType

instance Interp__pi CRepr R where interp__pi = GExpr $ CExprDouble pi


-- | Helpers for instances for which the dynamic operation is a named
-- C function.

unaryPrimCExpr' :: String -> CExpr R -> CExpr R
unaryPrimCExpr' fName = CExprDynamic . cDynFunCall fName . toCDynExpr

unaryPrimCExpr :: String -> CExpr (R -> R)
unaryPrimCExpr fName = CExprFun $ unaryPrimCExpr' fName

unaryCExprName :: (R -> R) -> String -> GExpr CRepr (R -> R)
unaryCExprName fstatic fName =
  unaryCExpr fstatic $ GExpr $ unaryPrimCExpr fName

binaryPrimCExpr :: String -> CExpr (R -> R -> R)
binaryPrimCExpr fName =
  CExprFun $ \x -> CExprFun $ \y -> CExprDynamic $
  cDynFunCall2 fName (toCDynExpr x) (toCDynExpr y)

binaryCExprName :: (R -> R -> R) -> String -> GExpr CRepr (R -> R -> R)
binaryCExprName fstatic fName =
  binaryCExpr fstatic $ GExpr $ binaryPrimCExpr fName


-- | Math functions

instance Interp__exp CRepr R where
  interp__exp = unaryCExprName exp "exp"

instance Interp__log CRepr R where
  interp__log = unaryCExprName log "log"

instance Interp__sqrt CRepr R where
  interp__sqrt = unaryCExprName sqrt "sqrt"

instance Interp__'times'times CRepr R where
  interp__'times'times = binaryCExprName (**) "pow"

instance Interp__logBase CRepr R where
  interp__logBase = binaryCExprName logBase "logBase"

instance Interp__sin CRepr R where
  interp__sin = unaryCExprName sin "sin"

instance Interp__cos CRepr R where
  interp__cos = unaryCExprName cos "cos"

instance Interp__tan CRepr R where
  interp__tan = unaryCExprName tan "tan"

instance Interp__asin CRepr R where
  interp__asin = unaryCExprName asin "asin"

instance Interp__acos CRepr R where
  interp__acos = unaryCExprName acos "acos"

instance Interp__atan CRepr R where
  interp__atan = unaryCExprName atan "atan"

instance Interp__sinh CRepr R where
  interp__sinh = unaryCExprName sinh "sinh"

instance Interp__cosh CRepr R where
  interp__cosh = unaryCExprName cosh "cosh"

instance Interp__tanh CRepr R where
  interp__tanh = unaryCExprName tanh "tanh"

instance Interp__asinh CRepr R where
  interp__asinh = unaryCExprName asinh "asinh"

instance Interp__acosh CRepr R where
  interp__acosh = unaryCExprName acosh "acosh"

instance Interp__atanh CRepr R where
  interp__atanh = unaryCExprName atanh "atanh"


-- | Probability expressions

-- instance Interp__realToProb CRepr where
--   interp__realToProb = unaryCExprFun realToProb cExprRealToProb

-- instance Interp__logRealToProb CRepr where
--   interp__logRealToProb = unaryCExprFun logRealToProb cExprLogRealToProb

-- instance Interp__probToReal CRepr where
--   interp__probToReal = unaryCExprFun probToReal cExprProbToReal

-- instance Interp__probToLogReal CRepr where
--   interp__probToLogReal = unaryCExprFun probToLogReal cExprProbToLogReal


-- | Distributions

instance Interp__normal CRepr where
  interp__normal =
    interp__'lam $ \(GExpr mu) -> interp__'lam $ \(GExpr sigma) ->
    GExpr $ CExprDist $ \(tp, v) -> return $ DoubleDist $ Log.Exp $
    cDynFunCall3 "normalPdf" (toCDynExpr mu) (toCDynExpr sigma)
    (VarExpr tp (VarName v))

instance Interp__uniform CRepr where
  interp__uniform =
    interp__'lam $ \(GExpr lb) -> interp__'lam $ \(GExpr ub) ->
    GExpr $ CExprDist $ \(tp, v) -> return $ DoubleDist $ Log.Exp $
    cDynFunCall3 "uniformPdf" (toCDynExpr lb) (toCDynExpr ub)
    (VarExpr tp (VarName v))

instance Interp__list_iid CRepr where
  interp__list_iid = interp__'lam $
    \(GExpr d) -> GExpr $ CExprDist $
    \((ListType tp), v) -> do
      dist <- projCDist d (tp, v)
      return $ ListDist dist

-- instance Interp__vec_iid CRepr where
--   interp__vec_iid = interp__'lam $ \(GExpr n) ->
--     interp__'lam $ \(GExpr d) -> GExpr $ CExprDist $
--     \((VecType tp), v) -> do
--       dist <- projCDist d (tp, v)
--       return $ VecDist (projCInt n) dist

