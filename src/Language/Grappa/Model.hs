{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, PolyKinds, ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

module Language.Grappa.Model where

import Control.Monad
import GHC.Exts

import Language.Grappa.Distribution

-- | FIXME: document this type
data ModelOp c a where
  MOpSample :: c d => d -> ModelOp c (Support d)
  MOpScore :: Prob -> ModelOp c ()

data ModelStep c r where
  ModelStep :: ModelOp c a -> (a -> r) -> ModelStep c r

-- | FIXME: document this type, and mention that it comes from Edward Kmett's
-- Control.Monad.Free.Church package
newtype Model (c :: * -> Constraint) a =
  Model { unModel :: forall r. (a -> r) -> (ModelStep c r -> r) -> r }

instance Functor (Model c) where
  fmap f m = m >>= return . f

instance Applicative (Model c) where
  pure = return
  (<*>) = ap

instance Monad (Model c) where
  return x = Model $ \kret _ -> kret x
  (Model m) >>= f =
    Model $ \kret kstep -> m (\x -> unModel (f x) kret kstep) kstep

-- | apply a 'ModelOp' to the current computation in a 'Model'
applyOp :: ModelOp c a -> Model c a
applyOp op = Model (\kret kstep -> kstep $ ModelStep op kret)

-- | Sample a distribution
sample :: c d => d -> Model c (Support d)
sample d = applyOp (MOpSample d)

-- | Observe a given piece of data against a distribution for it
observe :: PDFDist d => Support d -> d -> Model c ()
observe x d = weight $ distDensity d x

weight :: Prob -> Model c ()
weight w = applyOp $ MOpScore $ w

-- | Read a "variable", by either 'sample'ing or 'observe'ing
readVar :: (PDFDist d, c d) => Maybe (Support d) -> d -> Model c (Support d)
readVar (Just x) d = observe x d >> return x
readVar Nothing d = sample d


-- | The constructor-based free monad for 'Model' (FIXME: this is the Free type)
data DFAModel c a where
  DFAModelDone :: a -> DFAModel c a
  DFAModelStep :: ModelOp c b -> (b -> DFAModel c a) -> DFAModel c a

-- NOTE: we do not actually use the Monad instance for DFAModel, but it is nice
-- to know it is there...
instance Functor (DFAModel c) where
  fmap f m = m >>= return . f

instance Applicative (DFAModel c) where
  pure = return
  (<*>) = ap

instance Monad (DFAModel c) where
  return x = DFAModelDone x
  (DFAModelDone a) >>= f = f a
  (DFAModelStep op k) >>= f =
    DFAModelStep op $ \b -> k b >>= f

-- | Construct the 'DFAModel' from a 'Model'
dfaModel :: Model c a -> DFAModel c a
dfaModel (Model f) =
  f DFAModelDone $ \step ->
  case step of
    ModelStep op k -> DFAModelStep op $ \x -> k x

-- | FIXME: documentation
dfaModelDone :: DFAModel c a -> Maybe a
dfaModelDone (DFAModelDone a) = Just a
dfaModelDone (DFAModelStep _ _) = Nothing

dfaStateScore :: DFAModel c a -> Maybe Prob
dfaStateScore (DFAModelStep (MOpScore score) _) = Just score
dfaStateScore _ = Nothing

-- | FIXME: documentation
stepDFAModel :: Monad m => (forall b. ModelOp c b -> m b) ->
                DFAModel c a -> m (DFAModel c a)
stepDFAModel _ model@(DFAModelDone _) = return model
stepDFAModel stepOp (DFAModelStep op k) =
  stepOp op >>= return . k


-- *

data ReprModelOp (c :: ((* -> *) -> *) -> (* -> *) -> Constraint) f a where
  ReprOpSample :: c d f => !(d f) -> ReprModelOp c f (f (ReprSupport d))
  ReprOpScore :: c d f => !(d f) -> !(f (ReprSupport d)) -> ReprModelOp c f ()

data ReprModelStep c f r where
  ReprModelStep :: ReprModelOp c f a -> (a -> r) -> ReprModelStep c f r

-- | FIXME: document this type, and mention that it comes from Edward Kmett's
-- Control.Monad.Free.Church package
newtype ReprModel c f a =
  ReprModel { unReprModel :: forall r. (a -> r) -> (ReprModelStep c f r -> r) -> r }

-- | Apply a 'ModelOp' to the current computation in a 'Model'
applyOpRepr :: ReprModelOp c f a -> ReprModel c f a
applyOpRepr op = ReprModel (\kret kstep -> kstep $ ReprModelStep op kret)

-- | Sample a distribution
sampleRepr :: c d f => d f -> ReprModel c f (f (ReprSupport d))
sampleRepr d = applyOpRepr (ReprOpSample d)

-- | Observe a given piece of data against a distribution for it
observeRepr :: c d f => f (ReprSupport d) -> d f -> ReprModel c f ()
observeRepr x d = applyOpRepr (ReprOpScore d x)

-- -- | Read a "variable", by either 'sample'ing or 'observe'ing
-- readVarRepr :: (PDFDist d, c d) => Maybe (Support d) -> d -> Model c (Support d)
-- readVarRepr (Just x) d = observe x d >> return x
-- readVarRepr Nothing d = sample d

returnRepr :: a -> ReprModel d f a
returnRepr x = ReprModel $ \kret _ -> kret x

bindRepr :: ReprModel d f a -> (a -> ReprModel d f b) -> ReprModel d f b
bindRepr (ReprModel m) f =
  ReprModel $ \kret kstep -> m (\ x -> unReprModel (f x) kret kstep) kstep

thenRepr :: ReprModel d f a -> ReprModel d f b -> ReprModel d f b
thenRepr m n = m `bindRepr` \ _ -> n

instance Functor (ReprModel d f) where
  fmap f m = m >>= return . f

instance Applicative (ReprModel d f) where
  pure = return
  (<*>) = ap

instance Monad (ReprModel d f) where
  return = returnRepr
  (>>=) = bindRepr
