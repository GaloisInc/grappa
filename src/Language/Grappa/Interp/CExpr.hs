{-# LANGUAGE TypeFamilies, GADTs, RankNTypes, EmptyCase #-}
{-# LANGUAGE DataKinds, FlexibleInstances, TypeOperators #-}
{-# LANGUAGE DeriveAnyClass, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Language.Grappa.Interp.CExpr where

import           Data.Type.Equality
import qualified Numeric.Log as Log

import           Language.Grappa.Distribution
import           Language.Grappa.GrappaInternals


-- | The types of C expressions that we are targeting with our compiler
data CType a where
  DoubleType :: CType R
  IntType    :: CType Int
  BoolType   :: CType Bool
  TupleType  :: CTypes ts -> CType (ADT (TupleF ts))
  ListType   :: CType t -> CType (ADT (ListF t))

-- | An existentially-quantified 'CType'
data SomeCType = forall a. SomeCType (CType a)

-- | A heterogeneous list of 'CType's
type CTypes ts = HList CType ts

instance Show (CType a) where
  show DoubleType    = "DoubleType"
  show IntType       = "IntType"
  show BoolType      = "BoolType"
  show (TupleType _) = "TupleType"
  show (ListType _)  = "ListType"

-- | Typeclass for associating a 'CType' with a Haskell type
class HasCType a where cType :: CType a

instance HasCType Int where cType  = IntType
instance HasCType R where cType    = DoubleType
instance HasCType Prob where cType = error "HasCType: no CType Prob"
instance HasCType Bool where cType = BoolType
instance HasCTypes ts => HasCType (ADT (TupleF ts)) where
  cType = TupleType cTypes
instance HasCType t => HasCType (ADT (ListF t)) where
  cType = ListType cType

-- | Typeclass for associating a list of 'CType's with Haskell types
class HasCTypes ts where
  cTypes :: CTypes ts

instance HasCTypes '[] where cTypes = HListNil
instance (HasCType t, HasCTypes ts) => HasCTypes (t:ts) where
  cTypes = HListCons cType cTypes

-- | Test two 'CType's for equality, returning a Haskell type equality on
-- success and 'Nothing' on failure
cTypeEq :: CType a -> CType b -> Maybe (a :~: b)
cTypeEq DoubleType DoubleType = Just Refl
cTypeEq IntType IntType       = Just Refl
cTypeEq BoolType BoolType     = Just Refl
cTypeEq (TupleType as) (TupleType bs) =
  case cTypesEq as bs of
    Just Refl -> Just Refl
    _ -> Nothing
cTypeEq (ListType a) (ListType b) =
  case cTypeEq a b of
    Just Refl -> Just Refl
    _ -> Nothing
cTypeEq _ _ = Nothing

-- | Test two lists of 'CType's for equality
cTypesEq :: CTypes as -> CTypes bs -> Maybe (as :~: bs)
cTypesEq HListNil HListNil = Just Refl
cTypesEq (HListCons a as) (HListCons b bs) =
  case (cTypeEq a b, cTypesEq as bs) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
cTypesEq _ _ = Nothing

-- | Build a "proof" that there is no functional 'CType' by deriving any
-- arbitrary type @c@ from such a 'CType'
funCTypeFalse :: CType (a -> b) -> c
funCTypeFalse ty = case ty of { }

-- | Check if a 'CType' is a base type
isBaseType :: CType a -> Bool
isBaseType DoubleType = True
isBaseType IntType    = True
isBaseType BoolType   = True
isBaseType _          = False

-- | C expressions with a fixed, static value
data Literal
  = DoubleLit Double
  | IntLit Int
  | BoolLit Bool
  deriving Show

-- | A C variable
newtype VarName = VarName Int deriving Show

-- | A C function name
type FunName = String

-- | A C unary operation
data UnaryOp = NegateOp | NotOp
             deriving Show

-- | A C binary operation
data BinaryOp
  = PlusOp | TimesOp | MinusOp | DivOp | ExpOp
  | LtOp | LteOp | GtOp | GteOp | EqOp | NeOp
  | AndOp | OrOp
  deriving Show

-- | A dynamic expression, which is compiled to C
data CDynExpr a where
  LitExpr       :: CType a -> Literal -> CDynExpr a
  VarExpr       :: CType a -> VarName -> CDynExpr a
  UnaryExpr     :: UnaryOp -> CDynExpr a -> CDynExpr a
  BinaryExpr    :: CType ret -> BinaryOp -> CDynExpr a ->
                   CDynExpr a -> CDynExpr ret
  FunCallExpr   :: FunName -> CTypes args -> CType ret ->
                   CDynExprs args -> CDynExpr ret
  NamedVarExpr  :: CType a -> String -> CDynExpr a
  CondExpr      :: CDynExpr Bool -> CDynExpr a ->
                   CDynExpr a -> CDynExpr a
  TupleProjExpr :: CTypes as -> TypeListElem as a ->
                   CDynExpr (ADT (TupleF as)) -> CDynExpr a

-- | A list of C dynamic expressions, one of each type in @as@
type CDynExprs as = HList CDynExpr as

-- | Build a C expression for the literal constant @0@ at a given type
cDynZero :: CType a -> CDynExpr a
cDynZero IntType    = LitExpr IntType $ IntLit 0
cDynZero DoubleType = LitExpr DoubleType $ DoubleLit 0.0
cDynZero BoolType   = LitExpr BoolType $ BoolLit False
cDynZero _          = error "cDynZero: unsupported type"

-- | Build a C expression for the literal constant @1@ at a given type
cDynOne :: CType a -> CDynExpr a
cDynOne IntType    = LitExpr IntType $ IntLit 1
cDynOne DoubleType = LitExpr DoubleType $ DoubleLit 1.0
cDynOne BoolType   = LitExpr BoolType $ BoolLit True
cDynOne _          = error "cDynOne: unsupported type"

-- | Build a function call to a unary C function
cDynFunCall :: (HasCType a, HasCType b) => String -> CDynExpr a -> CDynExpr b
cDynFunCall fName arg =
  FunCallExpr fName (HListCons cType HListNil)
  cType (HListCons arg HListNil)

-- | Build a function call to a binary C function
cDynFunCall2 :: (HasCType a, HasCType b, HasCType c) =>
                String -> CDynExpr a -> CDynExpr b -> CDynExpr c
cDynFunCall2 fName arg1 arg2 =
  FunCallExpr fName (HListCons cType (HListCons cType HListNil))
  cType (HListCons arg1 (HListCons arg2 HListNil))

-- | Build a function call to a trinary C function
cDynFunCall3 :: (HasCType a, HasCType b, HasCType c, HasCType d) =>
                String -> CDynExpr a -> CDynExpr b -> CDynExpr c -> CDynExpr d
cDynFunCall3 fName arg1 arg2 arg3 =
  FunCallExpr fName
  (HListCons cType (HListCons cType (HListCons cType HListNil)))
  cType (HListCons arg1 (HListCons arg2 (HListCons arg3 HListNil)))

-- | Build a function call to the C @log@ function
cDynLog :: CDynExpr R -> CDynExpr R
cDynLog e = cDynFunCall "log" e

-- | Compute the type of a dynamic expression
cDynExprType :: CDynExpr a -> CType a
cDynExprType (LitExpr t _)               = t
cDynExprType (VarExpr t _)               = t
cDynExprType (UnaryExpr _ e)             = cDynExprType e
cDynExprType (BinaryExpr t _ _ _)        = t
cDynExprType (FunCallExpr _ _ t _)       = t
cDynExprType (NamedVarExpr t _)          = t
cDynExprType (CondExpr _ e _)            = cDynExprType e
cDynExprType (TupleProjExpr ts elemPf _) = projectHList ts elemPf

-- | A C representation of a distribution
data CDist a where
  -- | A distribution over 'Double's is just an expression for its PDF
  DoubleDist :: Log.Log (CDynExpr R) -> CDist R
  -- | A distribution over 'Int's is just an expression for its PDF
  IntDist    :: Log.Log (CDynExpr R) -> CDist Int
  -- | A distribution over 'Bool's is just an expression for its PDF
  BoolDist   :: Log.Log (CDynExpr R) -> CDist Bool
  -- | A distribution over tuples is a tuple of distributions, one for each
  -- element. Note that later distributions in the tuple have the values drawn
  -- from the earlier ones in scope.
  TupleDist  :: CDists as -> CDist (ADT (TupleF as))
  -- | A distribution over lists is a single distribution over the elements of
  -- the list. Note that this implicitly assumes that the length of the list is
  -- fixed at runtime.
  ListDist   :: CDist a -> CDist (ADT (ListF a))

-- | A heterogeneous list of C distributions
type CDists ts = HList CDist ts

-- | A C distribution of some unknown type
data SomeCDist = forall a. SomeCDist (CDist a)

-- | A list of C distributions of some unknown types
data SomeCDists = forall as. SomeCDists (CDists as)

-- | Convert a list of existentially quantified distributions to an
-- existentially quantified list of distributions
someCDistsOfList :: [SomeCDist] -> SomeCDists
someCDistsOfList [] = SomeCDists HListNil
someCDistsOfList (SomeCDist d : ds) =
  case someCDistsOfList ds of
    SomeCDists ds' -> SomeCDists (HListCons d ds')

-- | Build a tuple distribution from a list of distributions for the elements,
-- with the special case that a unary list is just itself
tupleCDist :: [SomeCDist] -> SomeCDist
tupleCDist [d] = d
tupleCDist ds  =
  case someCDistsOfList ds of
    SomeCDists ds' -> SomeCDist $ TupleDist ds'

-- | Convert a 'CDists' list to a list of 'SomeCDist's
cDistsToList :: CDists as -> [SomeCDist]
cDistsToList ds = hListToList SomeCDist ds

-- | Get the 'CType' of a C distribution
cDistType :: CDist a -> CType a
cDistType (DoubleDist _) = DoubleType
cDistType (IntDist _)    = IntType
cDistType (BoolDist _)   = BoolType
cDistType (TupleDist ds) = TupleType $ mapHList cDistType ds
cDistType (ListDist d)   = ListType $ cDistType d

-- | Get the 'CTypes' of a list of C distributions
cDistsTypes :: CDists as -> CTypes as
cDistsTypes ds = mapHList cDistType ds

{-
cDistBaseDist :: CDist a -> SomeCDist
cDistBaseDist (ListDist d) = SomeCDist d
cDistBaseDist _ = error "cDistBase: expected list or vec dist"
-}

-- | Extract the expression for the PDF of a distribution over a base type
cDistPDFExpr :: CDist a -> CDynExpr R
cDistPDFExpr (DoubleDist (Log.Exp e)) = e
cDistPDFExpr (IntDist (Log.Exp e)) = e
cDistPDFExpr (BoolDist (Log.Exp e)) = e
cDistPDFExpr _ = error "cDistPDFExpr: expected dist of base type"

-- | Get the (existentially-quantified) type of a 'SomeCDist'
someCDistType :: SomeCDist -> SomeCType
someCDistType (SomeCDist d) = SomeCType $ cDistType d

-- | Num, Fractional, and Floating instances for CDynExprs so that we
-- can use Numeric.Log to do log-space calculations.

-- instance HasCType a => Num (CDynExpr a) where
--   e1 + e2 = BinaryExpr cType PlusOp e1 e2
--   e1 - e2 = BinaryExpr cType MinusOp e1 e2
--   e1 * e2 = BinaryExpr cType TimesOp e1 e2
--   abs = error "Unimplemented CExpr op!"
--   signum = error "Unimplemented CExpr op!"
--   negate e      = UnaryExpr NegateOp e
--   fromInteger i = LitExpr cType (IntLit (fromInteger i))

-- instance HasCType a => Fractional (CDynExpr a) where
--   e1 / e2        = BinaryExpr cType DivOp e1 e2
--   fromRational r = LitExpr cType (DoubleLit (fromRational r))

-- instance (Floating a, HasCType a) => Floating (CDynExpr a) where
--   pi       = NamedVarExpr cType "pi"
--   exp e    = cDynFunCall "exp" e
--   log e    = cDynFunCall "log" e
--   sqrt e   = cDynFunCall "sqrt" e
--   e1 ** e2 = BinaryExpr cType ExpOp e1 e2
--   sin e    = cDynFunCall "sin" e
--   cos e    = cDynFunCall "cos" e
--   asin e   = cDynFunCall "asin" e
--   acos e   = cDynFunCall "acos" e
--   atan e   = cDynFunCall "atan" e
--   sinh e   = cDynFunCall "sinh" e
--   cosh e   = cDynFunCall "cosh" e
--   asinh e  = cDynFunCall "asinh" e
--   acosh e  = cDynFunCall "acosh" e
--   atanh e  = cDynFunCall "atanh" e
