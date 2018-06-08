{-# LANGUAGE TypeFamilies, GADTs, RankNTypes, EmptyCase #-}
{-# LANGUAGE DataKinds, FlexibleInstances, TypeOperators #-}
{-# LANGUAGE DeriveAnyClass, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Language.Grappa.Interp.CExprGADT where

import           Data.Type.Equality
import qualified Numeric.Log as Log

import           Language.Grappa.Distribution
import           Language.Grappa.GrappaInternals

-- | A (MapList f [t0, t1, ..., tn]) is a list containing n elements,
-- with each element i having type (f ti).
data MapList (f :: * -> *) (ts  :: [*]) where
  MapListNil  :: MapList f '[]
  MapListCons :: f a -> MapList f as -> MapList f (a ': as)

consTupleToMapList :: TupleF (t ': ts) f r -> MapList f (t ': ts)
consTupleToMapList tup = MapListCons (tupleHead tup)
                         (tupleToMapList (tupleTail tup))

tupleToMapList :: TupleF ts f r -> MapList f ts
tupleToMapList Tuple0 = MapListNil
tupleToMapList tup@(Tuple1 _)           = consTupleToMapList tup
tupleToMapList tup@(Tuple2 _ _)         = consTupleToMapList tup
tupleToMapList tup@(Tuple3 _ _ _)       = consTupleToMapList tup
tupleToMapList tup@(Tuple4 _ _ _ _)     = consTupleToMapList tup
tupleToMapList tup@(TupleN _ _ _ _ _ _) = consTupleToMapList tup

mapMapList :: (forall a. f a -> g a) -> MapList f as -> MapList g as
mapMapList _ MapListNil = MapListNil
mapMapList f (MapListCons a as) = MapListCons (f a) (mapMapList f as)

traverseMapList :: Applicative m => (forall a. f a -> m (g a)) ->
                   MapList f ts -> m (MapList g ts)
traverseMapList _ MapListNil = pure MapListNil
traverseMapList f (MapListCons x xs) =
  pure MapListCons <*> f x <*> traverseMapList f xs

traverseMapList' :: Applicative m => (forall a. f a -> m b) ->
                    MapList f ts -> m [b]
traverseMapList' _ MapListNil         = pure []
traverseMapList' f (MapListCons x xs) =
  pure (:) <*> f x <*> traverseMapList' f xs

foldMapList :: (forall a. f a -> b -> b) -> MapList f ts -> b -> b
foldMapList _ MapListNil acc         = acc
foldMapList g (MapListCons x xs) acc = g x $ foldMapList g xs acc

mapListLength :: MapList f ts -> Int
mapListLength l = foldMapList (const (+ 1)) l 0

buildMapListElems :: MapList f as -> MapList (TypeListElem as) as
buildMapListElems MapListNil = MapListNil
buildMapListElems (MapListCons _ rest) =
  MapListCons TypeListElem_Base (mapMapList TypeListElem_Cons
                                  (buildMapListElems rest))

projectMapList :: TypeListElem ts t -> MapList f ts -> f t
projectMapList TypeListElem_Base (MapListCons x _) = x
projectMapList (TypeListElem_Cons pf) (MapListCons _ rest) =
  projectMapList pf rest

mapListToTuple :: MapList f ts -> TupleF ts f r
mapListToTuple MapListNil = Tuple0
mapListToTuple (MapListCons x xs) = tupleCons x (mapListToTuple xs)

mapListToList :: (forall a. f a -> b) -> MapList f ts -> [b]
mapListToList _ MapListNil = []
mapListToList g (MapListCons x xs) = g x : mapListToList g xs

type family Concat (l1 :: [*]) (l2 :: [*]) where
  Concat '[] l = l
  Concat (x:xs) l = x : Concat xs l

mapListConcat :: MapList f as -> MapList f bs -> MapList f (Concat as bs)
mapListConcat MapListNil l = l
mapListConcat (MapListCons x xs) l = MapListCons x (mapListConcat xs l)

mapIMapList :: (forall a. f a -> Int -> b) -> MapList f as -> [b]
mapIMapList g l =
  snd $ foldMapList (\x (i, acc) -> (i+1, g x i : acc)) l (0, [])

zipWithList :: (forall a. f a -> b -> c) -> MapList f as -> [b] -> [c]
zipWithList g l1 l2 = zipWith ($) (mapListToList g l1) l2

zipWithList3 :: (forall a. f a -> b -> c -> d) ->
                MapList f as -> [b] -> [c] -> [d]
zipWithList3 g l1 l2 l3 = zipWith3 ($) (mapListToList g l1) l2 l3  

-- | The types of C expressions that we are targeting with our compiler
data CType a where
  DoubleType :: CType R
  IntType    :: CType Int
  BoolType   :: CType Bool
  TupleType  :: CTypes ts -> CType (ADT (TupleF ts))
  ListType   :: CType t -> CType (ADT (ListF t))

data SomeCType = forall a. SomeCType (CType a)
data SomeCTypes = forall as. SomeCTypes (CType as)

instance Show (CType a) where
  show DoubleType    = "DoubleType"
  show IntType       = "IntType"
  show BoolType      = "BoolType"
  show (TupleType _) = "TupleType"
  show (ListType _)  = "ListType"

class HasCType a where cType :: CType a
instance HasCType Int where cType  = IntType
instance HasCType R where cType    = DoubleType
instance HasCType Prob where cType = error "HasCType: no CType Prob"
instance HasCType Bool where cType = BoolType
instance HasCTypes ts => HasCType (ADT (TupleF ts)) where
  cType = TupleType cTypes
instance HasCType t => HasCType (ADT (ListF t)) where
  cType = ListType cType

class HasCTypes ts where
  cTypes :: CTypes ts
instance HasCTypes '[] where cTypes = MapListNil
instance (HasCType t, HasCTypes ts) => HasCTypes (t:ts) where
  cTypes = MapListCons cType cTypes

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

type CTypes ts = MapList CType ts

cTypesEq :: CTypes as -> CTypes bs -> Maybe (as :~: bs)
cTypesEq MapListNil MapListNil = Just Refl
cTypesEq (MapListCons a as) (MapListCons b bs) =
  case (cTypeEq a b, cTypesEq as bs) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
cTypesEq _ _ = Nothing

funCTypeFalse :: CType (a -> b) -> c
funCTypeFalse ty = case ty of

cTypesElem :: CTypes as -> TypeListElem as a -> CType a
cTypesElem (MapListCons t _) TypeListElem_Base = t
cTypesElem (MapListCons _ ts) (TypeListElem_Cons pf) = cTypesElem ts pf
cTypesElem MapListNil _ = error "cTypesElem: unexpected MapListNil"

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

newtype VarName = VarName Int deriving Show

type FunName = String

data UnaryOp = NegateOp | NotOp
             deriving Show

data BinaryOp
  = PlusOp | TimesOp | MinusOp | DivOp | ExpOp
  | LtOp | LteOp | GtOp | GteOp | EqOp | NeOp
  | AndOp | OrOp
  deriving Show

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

type CDynExprs as = MapList CDynExpr as

cDynZero :: CType a -> CDynExpr a
cDynZero IntType    = LitExpr IntType $ IntLit 0
cDynZero DoubleType = LitExpr DoubleType $ DoubleLit 0.0
cDynZero BoolType   = LitExpr BoolType $ BoolLit False
cDynZero _          = error "cDynZero: unsupported type"

cDynOne :: CType a -> CDynExpr a
cDynOne IntType    = LitExpr IntType $ IntLit 1
cDynOne DoubleType = LitExpr DoubleType $ DoubleLit 1.0
cDynOne BoolType   = LitExpr BoolType $ BoolLit True
cDynOne _          = error "cDynOne: unsupported type"

cDynFunCall :: (HasCType a, HasCType b) => String -> CDynExpr a -> CDynExpr b
cDynFunCall fName arg =
  FunCallExpr fName (MapListCons cType MapListNil)
  cType (MapListCons arg MapListNil)

cDynFunCall2 :: (HasCType a, HasCType b, HasCType c) =>
                String -> CDynExpr a -> CDynExpr b -> CDynExpr c
cDynFunCall2 fName arg1 arg2 =
  FunCallExpr fName (MapListCons cType (MapListCons cType MapListNil))
  cType (MapListCons arg1 (MapListCons arg2 MapListNil))

cDynFunCall3 :: (HasCType a, HasCType b, HasCType c, HasCType d) =>
                String -> CDynExpr a -> CDynExpr b -> CDynExpr c -> CDynExpr d
cDynFunCall3 fName arg1 arg2 arg3 =
  FunCallExpr fName
  (MapListCons cType (MapListCons cType (MapListCons cType MapListNil)))
  cType (MapListCons arg1 (MapListCons arg2 (MapListCons arg3 MapListNil)))

cDynLog :: CDynExpr R -> CDynExpr R
cDynLog e = cDynFunCall "log" e

cDynExprType :: CDynExpr a -> CType a
cDynExprType (LitExpr t _)               = t
cDynExprType (VarExpr t _)               = t
cDynExprType (UnaryExpr _ e)             = cDynExprType e
cDynExprType (BinaryExpr t _ _ _)        = t
cDynExprType (FunCallExpr _ _ t _)       = t
cDynExprType (NamedVarExpr t _)          = t
cDynExprType (CondExpr _ e _)            = cDynExprType e
cDynExprType (TupleProjExpr ts elemPf _) = projectMapList elemPf ts

data CDist a where
  DoubleDist :: Log.Log (CDynExpr R) -> CDist R
  IntDist    :: Log.Log (CDynExpr R) -> CDist Int
  BoolDist   :: Log.Log (CDynExpr R) -> CDist Bool
  TupleDist  :: CDists as -> CDist (ADT (TupleF as))
  ListDist   :: CDist a -> CDist (ADT (ListF a))

type CDists ts = MapList CDist ts

data SomeCDist = forall a. SomeCDist (CDist a)
data SomeCDists = forall as. SomeCDists (CDists as)

someCDist :: [SomeCDist] -> SomeCDist
someCDist [x] = x
someCDist ds  = tupleSomeCDists ds

someCDists :: [SomeCDist] -> SomeCDists
someCDists [] = SomeCDists MapListNil
someCDists (SomeCDist d : ds) =
  case someCDists ds of
    SomeCDists ds' ->
      SomeCDists (MapListCons d ds')

someCDists' :: CDists as -> [SomeCDist]
someCDists' ds = mapListToList SomeCDist ds

tupleSomeCDists :: [SomeCDist] -> SomeCDist
tupleSomeCDists ds =
  case someCDists ds of
    SomeCDists ds' -> SomeCDist $ TupleDist ds'

cDistType :: CDist a -> CType a
cDistType (DoubleDist _) = DoubleType
cDistType (IntDist _)    = IntType
cDistType (BoolDist _)   = BoolType
cDistType (TupleDist ds) = TupleType $ mapMapList cDistType ds
cDistType (ListDist d)   = ListType $ cDistType d

cDistsTypes :: CDists as -> CTypes as
cDistsTypes ds = mapMapList cDistType ds

cDistBaseDist :: CDist a -> SomeCDist
cDistBaseDist (ListDist d) = SomeCDist d
cDistBaseDist _ = error "cDistBase: expected list or vec dist"

cDistExpr :: CDist a -> CDynExpr R
cDistExpr (DoubleDist (Log.Exp e)) = e
cDistExpr (IntDist (Log.Exp e)) = e
cDistExpr (BoolDist (Log.Exp e)) = e
cDistExpr _ = error "cDistExpr: expected dist of base type"

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
