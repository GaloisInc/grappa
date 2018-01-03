{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Grappa.Interp.Supply where

import Data.Either
import Control.Monad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed as VU

import qualified Numeric.AD.Mode.Reverse as ADR


----------------------------------------------------------------------
-- * Immutable Supplies
----------------------------------------------------------------------

-- | The typeclass of "supplies" of values for real and/or discrete variables
class Supply supply where
  type SupplyReal supply :: *
  type SupplyInt supply :: *

  -- | Get the next real value and remaining supply after it, or raise an error
  -- if we have exhausted the supply or if a real does not come next
  supplyReal :: supply -> (SupplyReal supply, supply)

  -- | Get a list of the next @n@ real values
  supplyReals :: supply -> Int -> ([SupplyReal supply], supply)

  -- | Get the next integer value and remaining supply after it, or raise an
  -- error if we have exhausted the supply or if an integer does not come next
  supplyInt :: supply -> (SupplyInt supply, supply)

  -- | Get the next real value, using a monadic computation to supply values if
  -- we have run out
  supplyRealWithDefault ::
    Monad m => supply -> m (SupplyReal supply) -> m (SupplyReal supply, supply)

  -- | Get a list of the next @n@ real values, using a monadic computation to
  -- supply values if we have run out
  supplyRealsWithDefault ::
    Monad m => supply -> m (SupplyReal supply) -> Int ->
    m ([SupplyReal supply], supply)

  -- | Get the next integer value, using a monadic computation to supply one if
  -- we have run out of integers
  supplyIntWithDefault ::
    Monad m => supply -> m (SupplyInt supply) -> m (SupplyInt supply, supply)

  -- | Update a supply so that it contains the given sequence of reals and
  -- integers in the given order
  updateSupply :: supply -> SupplyUpdate supply -> supply

-- | The type of a list of updates for a given supply type
type SupplyUpdate supply = [Either (SupplyInt supply) (SupplyReal supply)]

-- | A supply of two vectors, one of reals and one of integers
data VectorSupply r i =
  VectorSupply (V.Vector r) Int (V.Vector i) Int

instance Supply (VectorSupply r i) where
  type SupplyReal (VectorSupply r i) = r
  type SupplyInt (VectorSupply r i) = i

  supplyReal (VectorSupply rs rix is iix) =
    if rix < V.length rs
    then (rs V.! rix, VectorSupply rs (rix+1) is iix)
    else error "VectorSupply: ran out of reals!"
  supplyReals (VectorSupply rs rix is iix) n =
    if rix + n <= V.length rs
    then (V.toList (V.slice rix n rs), VectorSupply rs (rix+n) is iix)
    else error "VectorSupply: ran out of reals!"
  supplyInt (VectorSupply rs rix is iix) =
    if iix < V.length is
    then (is V.! iix, VectorSupply rs rix is (iix+1))
    else error "VectorSupply: ran out of integers!"
  supplyRealWithDefault sup@(VectorSupply rs rix _ _) m =
    if rix < V.length rs then return (supplyReal sup) else (,sup) <$> m
  supplyRealsWithDefault (VectorSupply rs rix is iix) m n =
    do let num_left = V.length rs - rix
       let rets1 = V.toList $ V.slice rix (min n num_left) rs
       rets2 <- replicateM (n - num_left) m
       return (rets1 ++ rets2,
               VectorSupply rs (min (V.length rs) (rix + n)) is iix)
  supplyIntWithDefault sup@(VectorSupply _ _ is iix) m =
    if iix < V.length is then return (supplyInt sup) else (,sup) <$> m
  updateSupply (VectorSupply rs rix is iix) vals =
    VectorSupply
    (V.take rix rs V.++ V.fromList (rights vals)
     V.++ V.drop (rix + length (rights vals)) rs)
    rix
    (V.take iix is V.++ V.fromList (lefts vals)
     V.++ V.drop (iix + length (lefts vals)) is)
    iix

-- | Like 'VectorSupply' but using unboxed vectors
data UVectorSupply r i =
  UVectorSupply (VU.Vector r) Int (VU.Vector i) Int

instance (VU.Unbox r, VU.Unbox i) => Supply (UVectorSupply r i) where
  type SupplyReal (UVectorSupply r i) = r
  type SupplyInt (UVectorSupply r i) = i

  supplyReal (UVectorSupply rs rix is iix) =
    if rix < VU.length rs
    then (rs VU.! rix, UVectorSupply rs (rix+1) is iix)
    else error "UVectorSupply: ran out of reals!"
  supplyReals (UVectorSupply rs rix is iix) n =
    if rix + n <= VU.length rs
    then (VU.toList (VU.slice rix n rs), UVectorSupply rs (rix+n) is iix)
    else error "UVectorSupply: ran out of reals!"
  supplyInt (UVectorSupply rs rix is iix) =
    if iix < VU.length is
    then (is VU.! iix, UVectorSupply rs rix is (iix+1))
    else error "UVectorSupply: ran out of integers!"
  supplyRealWithDefault sup@(UVectorSupply rs rix _ _) m =
    if rix < VU.length rs then return (supplyReal sup) else (,sup) <$> m
  supplyRealsWithDefault (UVectorSupply rs rix is iix) m n =
    do let num_left = VU.length rs - rix
       let rets1 = VU.toList $ VU.slice rix (min n num_left) rs
       rets2 <- replicateM (n - num_left) m
       return (rets1 ++ rets2,
               UVectorSupply rs (min (VU.length rs) (rix + n)) is iix)
  supplyIntWithDefault sup@(UVectorSupply _ _ is iix) m =
    if iix < VU.length is then return (supplyInt sup) else (,sup) <$> m
  updateSupply (UVectorSupply rs rix is iix) vals =
    UVectorSupply
    (VU.take rix rs VU.++ VU.fromList (rights vals)
     VU.++ VU.drop (rix + length (rights vals)) rs)
    rix
    (VU.take iix is VU.++ VU.fromList (lefts vals)
     VU.++ VU.drop (iix + length (lefts vals)) is)
    iix

-- Dummy unboxed vector instances for storing reverse-mode gradients, that just
-- back-end into normal, boxed vectors
newtype instance VU.MVector s (ADR.Reverse rs a) =
  MV_ADReverse (MV.MVector s (ADR.Reverse rs a))
newtype instance VU.Vector    (ADR.Reverse rs a) =
  V_ADReverse  (V.Vector    (ADR.Reverse rs a))

-- "Unboxed" instance for Reverse-mode AD, where the "unboxed" representation is
-- just the boxed representation. FIXME: use or remove!
{-
instance VGen.Vector VU.Vector (ADR.Reverse rs a) where
  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicUnsafeFreeze (MV_ADReverse v) = V_ADReverse `liftM` V.unsafeFreeze v
  basicUnsafeThaw (V_ADReverse v) = MV_ADReverse `liftM` V.unsafeThaw v
  basicLength (V_ADReverse v) = V.length v
  basicUnsafeSlice i n (V_ADReverse v) = V_ADReverse $ V.unsafeSlice i n v
  basicUnsafeIndexM (V_ADReverse v) i = V.unsafeIndexM v i
  basicUnsafeCopy (MV_ADReverse mv) (V_ADReverse v) = V.unsafeCopy mv v
  elemseq _ = seq

instance MVGen.MVector VU.MVector (ADR.Reverse rs a) where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicOverlaps #-}
  {-# INLINE basicUnsafeNew #-}
  {-# INLINE basicInitialize #-}
  {-# INLINE basicUnsafeReplicate #-}
  {-# INLINE basicUnsafeRead #-}
  {-# INLINE basicUnsafeWrite #-}
  {-# INLINE basicClear #-}
  {-# INLINE basicSet #-}
  {-# INLINE basicUnsafeCopy #-}
  {-# INLINE basicUnsafeGrow #-}
  basicLength (MV_ADReverse v) = MV.length v
  basicUnsafeSlice i n (MV_ADReverse v) = MV_ADReverse $ MV.unsafeSlice i n v
  basicOverlaps (MV_ADReverse v1) (MV_ADReverse v2) = MV.overlaps v1 v2
  basicUnsafeNew n = MV_ADReverse `liftM` MV.unsafeNew n
  basicInitialize (MV_ADReverse _) = return ()
  basicUnsafeReplicate n x = MV_ADReverse `liftM` MV.replicate n x
  basicUnsafeRead (MV_ADReverse v) i = MV.unsafeRead v i
  basicUnsafeWrite (MV_ADReverse v) i x = MV.unsafeWrite v i x
  basicClear (MV_ADReverse v) = MV.clear v
  basicSet (MV_ADReverse v) x = MV.set v x
  basicUnsafeCopy (MV_ADReverse v1) (MV_ADReverse v2) = MV.unsafeCopy v1 v2
  basicUnsafeMove (MV_ADReverse v1) (MV_ADReverse v2) = MV.unsafeMove v1 v2
  basicUnsafeGrow (MV_ADReverse v) n = MV_ADReverse `liftM` MV.unsafeGrow v n

instance VU.Unbox (ADR.Reverse rs a)
-}


-- | A tree-shaped supply, where each discrete (i.e., integer) choice can lead
-- to a different branch of the tree
data TreeSupply r
  = NodeReal r (TreeSupply r)
  | NodeInt
    !Int {-^ Branch choice. INVARIANT: the int falls within [0,length branches) -}
    [TreeSupply r] {-^ Branches -}
  | NodeEmpty

instance Supply (TreeSupply r) where
  type SupplyReal (TreeSupply r) = r
  type SupplyInt (TreeSupply r) = Int

  supplyReal (NodeReal r next) = (r, next)
  supplyReal (NodeInt _ _) = error "TreeSupply: expected a real, found an int!"
  supplyReal NodeEmpty = error "TreeSupply: ran out of reals!"

  supplyReals supply 0 = ([], supply)
  supplyReals supply n =
    let (r, supply') = supplyReal supply
        (rs, supply'') = supplyReals supply' (n-1) in
    (r:rs, supply'')

  supplyInt (NodeReal _ _) = error "TreeSupply: expected an int, found a real!"
  supplyInt (NodeInt i nexts) = (i, nexts!!i)
  supplyInt NodeEmpty = error "TreeSupply: ran out of integers!"

  supplyRealWithDefault NodeEmpty m = (,NodeEmpty) <$> m
  supplyRealWithDefault sup _ = return (supplyReal sup)

  supplyRealsWithDefault sup _ 0 = return ([], sup)
  supplyRealsWithDefault NodeEmpty m n =
    (, NodeEmpty) <$> replicateM n m
  supplyRealsWithDefault sup m n =
    do let (r, sup') = supplyReal sup
       (rs, sup'') <- supplyRealsWithDefault sup' m (n-1)
       return (r:rs, sup'')

  supplyIntWithDefault NodeEmpty m = (,NodeEmpty) <$> m
  supplyIntWithDefault sup _ = return (supplyInt sup)

  updateSupply sup [] = sup
  updateSupply NodeEmpty (Left i:vals) =
    NodeInt i (replicate i NodeEmpty ++ [updateSupply NodeEmpty vals])
  updateSupply NodeEmpty (Right r:vals) =
    NodeReal r (updateSupply NodeEmpty vals)
  updateSupply (NodeInt _ nodes) (Left i':vals) =
    if i' < length nodes then
      NodeInt i' (take i' nodes ++ [updateSupply (nodes !! i') vals]
                  ++ drop (i' + 1) nodes)
    else
      NodeInt i' (nodes ++ replicate (i' - length nodes) NodeEmpty
                  ++ [updateSupply (nodes !! i') vals])
  updateSupply (NodeInt _ _) (Right _:_) =
    error "TreeSupply (update): expected a real, found an int!"
  updateSupply (NodeReal _ node) (Right r':vals) =
    NodeReal r' (updateSupply node vals)
  updateSupply (NodeReal _ _) (Left _:_) =
    error "TreeSupply (update): expected an int, found a real!"
