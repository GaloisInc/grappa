{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Grappa.Interp.BayesNet where

import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals
import Language.Grappa.Interp
import Language.Grappa.Rand.MWCRandM
import Language.Grappa.Frontend.DataSource
import Language.Grappa.Interp.MonoidRepr
import Language.Grappa.Interp.ProductRepr
import Language.Grappa.Interp.FunRepr
import Language.Grappa.Interp.StandardHORepr
import Language.Grappa.Interp.ADHORepr

import qualified Numeric.Log as Log

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

import Control.Monad.State

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- import Data.IntMap.Strict (IntMap)
-- import qualified Data.IntMap.Strict as IntMap

-- import qualified Numeric.AD.Mode.Reverse as ADR
-- import qualified Numeric.AD.Internal.Reverse as ADR (Tape)
-- import Data.Reflection (Reifies)

import qualified Data.Vector as V

import Control.Monad.ST
import qualified Data.Vector.Mutable as MV


----------------------------------------------------------------------
-- * Variables in Bayesian Networks
----------------------------------------------------------------------

-- | The types of variable names / node names in a Bayesian network
data BNVarType a where
  BNTypeInt :: BNVarType Int
  BNTypeReal :: BNVarType R
  BNTypeUnit :: BNVarType ()

-- | Variable names in a Bayesian network are just integers with a type tag
data BNVar a = BNVar { bnVarType :: BNVarType a, bnVarIndex :: Int }

instance Show (BNVar a) where
  show (BNVar BNTypeInt i) = "i" ++ show i
  show (BNVar BNTypeReal i) = "r" ++ show i
  show (BNVar BNTypeUnit i) = "u" ++ show i

-- | Build an integer variable from its index
mkIntVar :: Int -> BNVar Int
mkIntVar = BNVar BNTypeInt

-- | Build a real variable from its index
mkRealVar :: Int -> BNVar R
mkRealVar = BNVar BNTypeReal

-- | Build a unit variable from its index
mkUnitVar :: Int -> BNVar ()
mkUnitVar = BNVar BNTypeUnit

-- | A variable name of unknown type
data SomeBNVar = forall a. SomeBNVar (BNVar a)

instance Eq (BNVar a) where
  var1 == var2 = bnVarIndex var1 == bnVarIndex var2

instance Ord (BNVar a) where
  compare var1 var2 = compare (bnVarIndex var1) (bnVarIndex var2)

-- | A set of variable names
data BNVars = BNVars { bnVarsIntVars :: IntSet,
                       bnVarsRealVars :: IntSet,
                       bnVarsUnitVars :: IntSet } deriving Eq

-- | Get the integer variables in a set as a list
bnVarsIntVarsList :: BNVars -> [BNVar Int]
bnVarsIntVarsList vars = map mkIntVar $ IntSet.toList $ bnVarsIntVars vars

-- | The empty variable set
emptyBNVars :: BNVars
emptyBNVars = BNVars { bnVarsIntVars = IntSet.empty,
                       bnVarsRealVars = IntSet.empty,
                       bnVarsUnitVars = IntSet.empty }

-- | Insert a variable into a set
insertBNVars :: BNVar a -> BNVars -> BNVars
insertBNVars (BNVar BNTypeInt ix) vars =
  vars { bnVarsIntVars = IntSet.insert ix $ bnVarsIntVars vars }
insertBNVars (BNVar BNTypeReal ix) vars =
  vars { bnVarsRealVars = IntSet.insert ix $ bnVarsRealVars vars }
insertBNVars (BNVar BNTypeUnit ix) vars =
  vars { bnVarsUnitVars = IntSet.insert ix $ bnVarsUnitVars vars }

-- | The variable set containing a single variable
singletonBNVars :: BNVar a -> BNVars
singletonBNVars var = insertBNVars var emptyBNVars

-- | Test if a given variable is in a variable set
memberBNVars :: BNVar a -> BNVars -> Bool
memberBNVars (BNVar BNTypeInt ix) = IntSet.member ix . bnVarsIntVars
memberBNVars (BNVar BNTypeReal ix) = IntSet.member ix . bnVarsRealVars
memberBNVars (BNVar BNTypeUnit ix) = IntSet.member ix . bnVarsUnitVars

-- | Take the union of two variable sets
unionBNVars :: BNVars -> BNVars -> BNVars
unionBNVars vars1 vars2 =
  BNVars { bnVarsIntVars =
             IntSet.union (bnVarsIntVars vars1) (bnVarsIntVars vars2),
           bnVarsRealVars =
             IntSet.union (bnVarsRealVars vars1) (bnVarsRealVars vars2),
           bnVarsUnitVars =
             IntSet.union (bnVarsUnitVars vars1) (bnVarsUnitVars vars2) }

-- | Fold integer and real functions over a variable set
foldBNVars :: (forall a. BNVar a -> b -> b) -> b -> BNVars -> b
foldBNVars f z vars =
  flip (IntSet.foldr (f . BNVar BNTypeInt)) (bnVarsIntVars vars) $
  flip (IntSet.foldr (f . BNVar BNTypeReal)) (bnVarsRealVars vars) $
  flip (IntSet.foldr (f . BNVar BNTypeUnit)) (bnVarsUnitVars vars) $
  z

instance Monoid BNVars where
  mempty = emptyBNVars
  mappend = unionBNVars

-- | An assignment of 'Int's and 'Double's to variables of those types
data BNAssign r =
  BNAssign { bnInts :: V.Vector Int,
             bnReals :: V.Vector r }
  deriving (Functor, Foldable, Traversable, Show)

-- | The empty assignment
emptyBNAssign :: BNAssign r
emptyBNAssign = BNAssign V.empty V.empty

-- | The empty assignment with a given number of integer and real variables
emptyBNAssignLen :: Int -> Int -> BNAssign r
emptyBNAssignLen is rs =
  BNAssign (V.replicate is $ error "Uninitialized variable value")
  (V.replicate rs $ error "Uninitialized variable value")

-- | Look up an 'Int' in a variable assignment
lookupIntBNAssign :: BNVar Int -> BNAssign r -> Int
lookupIntBNAssign var assgn = bnInts assgn V.! bnVarIndex var

-- | Look up a 'Double' in a variable assignment
lookupRealBNAssign :: BNVar R -> BNAssign r -> r
lookupRealBNAssign var assgn = bnReals assgn V.! bnVarIndex var

type family BNAssignRet r a where
  BNAssignRet r Int = Int
  BNAssignRet r R = r
  BNAssignRet r () = ()

-- | Look up an arbitrary value in a variable assignment
lookupBNAssign :: BNVar a -> BNAssign r -> BNAssignRet r a
lookupBNAssign var@(BNVar BNTypeInt _) = lookupIntBNAssign var
lookupBNAssign var@(BNVar BNTypeReal _) = lookupRealBNAssign var
lookupBNAssign (BNVar BNTypeUnit _) = \_ -> ()

-- | Set an 'Int' value in a variable assignment
setIntBNAssign :: BNVar Int -> Int -> BNAssign r -> BNAssign r
setIntBNAssign var val assgn =
  assgn { bnInts = bnInts assgn V.// [(bnVarIndex var,val)] }

-- | Set a real value in a variable assignment
setRealBNAssign :: BNVar R -> r -> BNAssign r -> BNAssign r
setRealBNAssign var val assgn =
  assgn { bnReals = bnReals assgn V.// [(bnVarIndex var,val)] }

-- | Bulk set all the real values in an assignment
setAllRealsBNAssign :: BNAssign r -> V.Vector r -> BNAssign r
setAllRealsBNAssign asgn reals
  | V.length (bnReals asgn) == V.length reals = asgn { bnReals = reals }
setAllRealsBNAssign _ _ = error "setAllRealsBNAssign"

-- | An assignment to just a set of integer variables
newtype BNIntAssign = BNIntAssign { unBNIntAssign :: [(BNVar Int, Int)] }

-- | The empty integer assignment
emptyBNIntAssign :: BNIntAssign
emptyBNIntAssign = BNIntAssign []

-- | Add a (variable, value) pair to an integer assignment
addBNIntAssign :: BNIntAssign -> BNVar Int -> Int -> BNIntAssign
addBNIntAssign (BNIntAssign asgn) var val = BNIntAssign $ (var,val):asgn

-- | Bulk set a list of integer values in a variable assignment
setIntsBNAssign :: BNIntAssign -> BNAssign r -> BNAssign r
setIntsBNAssign (BNIntAssign var_vals) assgn =
  assgn { bnInts = bnInts assgn V.// map (\(var,val) ->
                                           (bnVarIndex var, val)) var_vals }

-- | A gradient of the real-valued variables in an assignment relative to a
-- log-PDF function
newtype BNAssignGrad = BNAssignGrad { unBNAssignGrad :: V.Vector Double }

-- | Sum the values in a set of assignment gradients. This is the correct way to
-- combine them, as they represent the gradients of log-PDF functions where the
-- PDFs are being multiplied, i.e., the logs are being summed. Assume that the
-- assignment gradients all have the same size, and that there is at least one
-- of them.
sumBNAssignGrad :: [BNAssignGrad] -> BNAssignGrad
sumBNAssignGrad [] = error "sumBNAssignGrad: empty list"
sumBNAssignGrad grads@(grad1 : _) =
  BNAssignGrad $ V.generate (V.length $ unBNAssignGrad grad1) $
  \ix -> sum $ map ((V.! ix) . unBNAssignGrad) grads


----------------------------------------------------------------------
-- Instances for the MonoidRepr BNVars representation
----------------------------------------------------------------------

instance EmbedRepr (MonoidRepr BNVars) Bool where
  embedRepr _ = interp__'bottom
instance EmbedRepr (MonoidRepr BNVars) Int where
  embedRepr _ = interp__'bottom
instance EmbedRepr (MonoidRepr BNVars) R where
  embedRepr _ = interp__'bottom
instance EmbedRepr (MonoidRepr BNVars) Prob where
  embedRepr _ = interp__'bottom


----------------------------------------------------------------------
-- * Values Inside a Bayesian Network Node
----------------------------------------------------------------------

-- | The empty type as a monad
data VoidM a

instance Functor VoidM where fmap _ v = case v of { }

instance Applicative VoidM where
  pure = return
  (<*>) = ap

instance Monad VoidM where
  return _ = error "VoidM return"
  m >>= _ = case m of { }

-- | The representation used for the return value of a dynamic expression
type BNDynRetRepr = StandardHORepr VoidM Double Int

-- | The representation type function used by 'BNDynRetRepr'
type BNDynRetReprF a = StandardHOReprF VoidM Double Int a

-- | The type tag for representing dynamic expressions, which have a set of
-- variables that are free and can compute values relative to an assignment,
-- both using and not using AD
type BNDynRepr =
  ProductRepr (MonoidRepr BNVars)
  (ProductRepr (FunRepr (BNAssign Double) BNDynRetRepr)
   (ADHORepr VoidM BNAssign))

-- | Destruct the empty type that is a dynamic representation of a distribution
noDynDist :: GExpr BNDynRepr (Dist a) -> b
noDynDist (GExpr (_, (d, _))) =
  case d emptyBNAssign VParam of { }

-- | Build an expression that looks up an integer variable value
intVarBNDynExpr :: BNVar Int -> GExpr BNDynRepr Int
intVarBNDynExpr var =
  GExpr (singletonBNVars var,
         (lookupIntBNAssign var, ADExpr (GExpr . lookupIntBNAssign var)))

-- | Build an expression that looks up a real variable value
realVarBNDynExpr :: BNVar R -> GExpr BNDynRepr R
realVarBNDynExpr var =
  GExpr (singletonBNVars var,
         (lookupRealBNAssign var, ADExpr (GExpr . lookupRealBNAssign var)))

-- | Extract the dependencies of an expression
bnExprDeps :: GExpr BNDynRepr a -> BNVars
bnExprDeps (GExpr (deps, _)) = deps

-- | Evaluate a dynamic expression relative to an assignment
evalDynExpr :: GExpr BNDynRepr a -> BNAssign Double -> BNDynRetReprF a
evalDynExpr e = unGExpr . flip applyFunRepr (projProduct1 (projProduct2 e))

-- | Extract a probability function for each assignment from an expression
bnExprProbFun :: GExpr BNDynRepr Prob -> BNAssign Double -> Prob
bnExprProbFun (GExpr (_, (prob_fun, _))) = Prob . prob_fun

-- | Extract the gradient of 'bnExprProbFun' from an expression
bnExprProbFunGrad :: GExpr BNDynRepr Prob -> BNAssign Double -> BNAssignGrad
bnExprProbFunGrad (GExpr (_, (_, ad_prob_fun))) =
  BNAssignGrad . bnReals . gradProbADHORepr (GExpr ad_prob_fun)

data PDF a =
  PDF { pdfProb :: BNAssign Double -> a -> Prob,
        pdfProbGrad :: BNAssign Double -> a -> BNAssignGrad }

-- | Extract a PDF from a function to expressions of type 'Prob'
bnExprPDF :: (a -> GExpr BNDynRepr Prob) -> PDF a
bnExprPDF expr_f =
  PDF { pdfProb = \asgn a -> bnExprProbFun (expr_f a) asgn,
        pdfProbGrad = \asgn a -> bnExprProbFunGrad (expr_f a) asgn }


----------------------------------------------------------------------
-- * Partially-Built Bayesian Networks
----------------------------------------------------------------------

data IntBayesNode =
  IntBayesNode { intNodeDeps :: BNVars,
                 intNodeCardinality :: Int,
                 intNodePDF :: PDF Int }

mkIntBayesNode :: [GExpr BNDynRepr Prob] -> IntBayesNode
mkIntBayesNode prob_exprs =
  IntBayesNode { intNodeDeps = mconcat (map bnExprDeps prob_exprs),
                 intNodeCardinality = length prob_exprs,
                 intNodePDF = bnExprPDF (prob_exprs !!)}

data RealBayesNode =
  RealBayesNode { realNodeDeps :: BNVars,
                  realNodeSampler :: BNAssign Double -> MWCRandM Double,
                  -- ^ NOTE: this only samples from the prio of the value of a
                  -- node, i.e., it does not take posterior data into account
                  realNodePDF :: PDF Double }

mkRealBayesNode :: (BNAssign Double -> MWCRandM Double) ->
                   (GExpr BNDynRepr R -> GExpr BNDynRepr Prob) ->
                   RealBayesNode
mkRealBayesNode sampler exprF =
  RealBayesNode { realNodeDeps = bnExprDeps $ exprF interp__'bottom,
                  realNodeSampler = sampler,
                  realNodePDF = bnExprPDF (exprF . embedRepr) }

-- | A unit node is a node with a set value (which is not captured in the node),
-- whose only contribution is its probability dependent on the assignment
data UnitBayesNode =
  UnitBayesNode { unitNodeDeps :: BNVars,
                  unitNodePDF :: PDF () }

mkUnitBayesNode :: GExpr BNDynRepr Prob -> UnitBayesNode
mkUnitBayesNode expr =
  UnitBayesNode { unitNodeDeps = bnExprDeps expr,
                  unitNodePDF = bnExprPDF (\_ -> expr) }

-- | A partially-built Bayesian network, which stores the nodes in reverse order
-- for efficiency of construction
data PartialBayesNet =
  PartialBayesNet
  { pbnRevIntNodes :: [IntBayesNode],
    pbnRevRealNodes :: [RealBayesNode],
    pbnRevUnitNodes :: [UnitBayesNode],
    pbnRevNodeNames :: [SomeBNVar]
  }

-- | The empty Bayesian network
emptyPBN :: PartialBayesNet
emptyPBN = PartialBayesNet [] [] [] []

-- | Insert an integer node into a partial Bayesian network, returning the new
-- network and also the index of the newly-inserted node
insertIntNodePBN :: IntBayesNode -> PartialBayesNet -> (Int, PartialBayesNet)
insertIntNodePBN node pbn =
  (length (pbnRevIntNodes pbn),
   pbn { pbnRevIntNodes = node : pbnRevIntNodes pbn,
         pbnRevNodeNames =
           SomeBNVar (BNVar BNTypeInt (length $ pbnRevIntNodes pbn)) :
           pbnRevNodeNames pbn })

-- | Insert a real node into a partial Bayesian network, returning the new
-- network and also the index of the newly-inserted node
insertRealNodePBN :: RealBayesNode -> PartialBayesNet -> (Int, PartialBayesNet)
insertRealNodePBN node pbn =
  (length (pbnRevRealNodes pbn),
   pbn { pbnRevRealNodes = node : pbnRevRealNodes pbn,
         pbnRevNodeNames =
           SomeBNVar (BNVar BNTypeReal (length $ pbnRevRealNodes pbn)) :
           pbnRevNodeNames pbn })

-- | Insert a unit node into a partial Bayesian network, returning the new
-- network and also the index of the newly-inserted node
insertUnitNodePBN :: UnitBayesNode -> PartialBayesNet -> (Int, PartialBayesNet)
insertUnitNodePBN node pbn =
  (length (pbnRevUnitNodes pbn),
   pbn { pbnRevUnitNodes = node : pbnRevUnitNodes pbn,
         pbnRevNodeNames =
           SomeBNVar (BNVar BNTypeUnit (length $ pbnRevUnitNodes pbn)) :
           pbnRevNodeNames pbn })


----------------------------------------------------------------------
-- * Bayesian Networks
----------------------------------------------------------------------

data BayesNet a =
  BayesNet
  { bnIntNodes :: V.Vector IntBayesNode,
    bnRealNodes :: V.Vector RealBayesNode,
    bnUnitNodes :: V.Vector UnitBayesNode,
    bnIntForwardDeps :: V.Vector BNVars,
    bnRealForwardDeps :: V.Vector BNVars,
    bnTopoSorted :: [SomeBNVar],
    bnTopExpr :: BNExpr a
  }

type family BayesNodeType a where
  BayesNodeType Int = IntBayesNode
  BayesNodeType R = RealBayesNode
  BayesNodeType () = UnitBayesNode

-- | Get a list of all integer variables in a network
bnIntVars :: BayesNet a -> [BNVar Int]
bnIntVars net = map mkIntVar [0 .. length (bnIntNodes net) - 1]

-- | Get a list of all unit variables in a network
bnUnitVars :: BayesNet a -> [BNVar ()]
bnUnitVars net = map mkUnitVar [0 .. length (bnUnitNodes net) - 1]

-- | Look up a node in a Bayesian network
bnLookupNode :: BayesNet a -> BNVar b -> BayesNodeType b
bnLookupNode net (BNVar BNTypeInt ix) = bnIntNodes net V.! ix
bnLookupNode net (BNVar BNTypeReal ix) = bnRealNodes net V.! ix
bnLookupNode net (BNVar BNTypeUnit ix) = bnUnitNodes net V.! ix

-- | Look up the cardinality of an integer node
bnNodeCardinality :: BayesNet a -> BNVar Int -> Int
bnNodeCardinality net var = intNodeCardinality $ bnLookupNode net var

-- | Look up the dependencies of a node in a Bayesian network by variable name
bnLookupNodeDeps :: BayesNet a -> BNVar b -> BNVars
bnLookupNodeDeps net var@(BNVar BNTypeInt _) =
  intNodeDeps $ bnLookupNode net var
bnLookupNodeDeps net var@(BNVar BNTypeReal _) =
  realNodeDeps $ bnLookupNode net var
bnLookupNodeDeps net var@(BNVar BNTypeUnit _) =
  unitNodeDeps $ bnLookupNode net var

-- | Lookup just the integer node dependencies of a node
bnLookupNodeIntDeps :: BayesNet a -> BNVar b -> [BNVar Int]
bnLookupNodeIntDeps net var = bnVarsIntVarsList $ bnLookupNodeDeps net var

-- | Test if the second variable is in the dependencies of the first
bnDepsMember :: BayesNet a -> BNVar b -> BNVar c -> Bool
bnDepsMember net var in_var = memberBNVars in_var (bnLookupNodeDeps net var)

-- | Get the forward dependencies from an integer node to other integer nodes
bnIntIntForwardDeps :: BayesNet a -> BNVar Int -> [BNVar Int]
bnIntIntForwardDeps net var =
  map (BNVar BNTypeInt) $ IntSet.toList $
  bnVarsIntVars (bnIntForwardDeps net V.! bnVarIndex var)

-- | Look up the PDF of a node
bnLookupNodePDF :: BayesNet a -> BNVar b -> PDF (BNAssignRet Double b)
bnLookupNodePDF net var@(BNVar BNTypeInt _) =
  intNodePDF $ bnLookupNode net var
bnLookupNodePDF net var@(BNVar BNTypeReal _) =
  realNodePDF $ bnLookupNode net var
bnLookupNodePDF net var@(BNVar BNTypeUnit _) =
  unitNodePDF $ bnLookupNode net var

-- | Evaluate the PDF of a node given its name and an assignment
evalNodePDF :: BayesNet a -> BNAssign Double -> BNVar b -> Prob
evalNodePDF net asgn var =
  nanProtect $ pdfProb (bnLookupNodePDF net var) asgn (lookupBNAssign var asgn)
  where
    nanProtect x
      | probIsNaN x = error $ "evalNodePDF: NaN! var = " ++ show var
    nanProtect x = x

-- | Evaluate the PDF of a node given its name and an assignment
evalSomeNodePDF :: BayesNet a -> BNAssign Double -> SomeBNVar -> Prob
evalSomeNodePDF net asgn (SomeBNVar var) = evalNodePDF net asgn var

-- | Evaluate the gradient of the PDF of a node given its name and an assignment
evalNodePDFGrad :: BayesNet a -> BNAssign Double -> BNVar b -> BNAssignGrad
evalNodePDFGrad net asgn var =
  pdfProbGrad (bnLookupNodePDF net var) asgn (lookupBNAssign var asgn)

-- | Evaluate the gradient of the PDF of a node given its name and an assignment
evalSomeNodePDFGrad :: BayesNet a -> BNAssign Double -> SomeBNVar -> BNAssignGrad
evalSomeNodePDFGrad net asgn (SomeBNVar var) = evalNodePDFGrad net asgn var

-- | Evaluate the probability distribution of an integer node given an
-- assignment to variables it depends on
evalIntNodeProbs :: BayesNet a -> BNAssign Double -> BNVar Int -> [Prob]
evalIntNodeProbs net asgn var =
  map (pdfProb (bnLookupNodePDF net var) asgn)
  [0 .. bnNodeCardinality net var - 1]

-- | Evaluate the top-level expression of a Bayes net, given an assignment. This
-- assumes that the type @a@ is a dynamic type, i.e., does not contain 'Dist'.
bnEval :: BayesNet a -> BNAssign Double -> BNDynRetReprF a
bnEval net = evalDynExpr (bnExprToDyn (GExpr $ bnTopExpr net))

-- | Evaluate the entire log PDF of a Bayes net, given an assignment
bnEvalPDF :: BayesNet a -> BNAssign Double -> Prob
bnEvalPDF net asgn = product $ map (evalSomeNodePDF net asgn) (bnTopoSorted net)

-- | Evaluate the entire gradient of the log PDF of a Bayes net
bnEvalPDFGrad :: BayesNet a -> BNAssign Double -> BNAssignGrad
bnEvalPDFGrad net asgn =
  sumBNAssignGrad $ map (evalSomeNodePDFGrad net asgn) (bnTopoSorted net)

-- | "Complete" a partially-built Bayesian network, by filling in the forward
-- dependencies, reversing the lists of nodes, and putting the nodes in vectors
completeBayesNet :: BNExpr a -> PartialBayesNet -> BayesNet a
completeBayesNet bnTopExpr pbn = runST $ do
  -- Build the vectors of nodes
  let bnIntNodes = V.fromList $ reverse $ pbnRevIntNodes pbn
      bnRealNodes = V.fromList $ reverse $ pbnRevRealNodes pbn
      bnUnitNodes = V.fromList $ reverse $ pbnRevUnitNodes pbn
      bnTopoSorted = reverse $ pbnRevNodeNames pbn

  -- Build mutable vectors for calculating forward dependencies
  int_forward_deps :: MV.MVector s BNVars <-
    MV.replicate (length $ pbnRevIntNodes pbn) emptyBNVars
  real_forward_deps <-
    MV.replicate (length $ pbnRevRealNodes pbn) emptyBNVars

  -- Add forward dependency links from all the vars in the set to the given var
  let add_forward_deps :: BNVars -> BNVar a -> ST s ()
      add_forward_deps deps var =
        foldBNVars
        (\ dep_var m ->
          case dep_var of
            BNVar BNTypeInt ix ->
              MV.modify int_forward_deps (insertBNVars var) ix >> m
            BNVar BNTypeReal ix ->
              MV.modify real_forward_deps (insertBNVars var) ix >> m
            _ -> m)
        (return ()) deps

  -- Add the forward dependencies
  V.imapM_ (\ix node ->
             add_forward_deps (intNodeDeps node) (BNVar BNTypeInt ix))
    bnIntNodes
  V.imapM_ (\ix node ->
             add_forward_deps (realNodeDeps node) (BNVar BNTypeReal ix))
    bnRealNodes
  V.imapM_ (\ix node ->
             add_forward_deps (unitNodeDeps node) (BNVar BNTypeUnit ix))
    bnUnitNodes

  -- Collect the forward dependencies and return the full Bayesian network
  bnIntForwardDeps <- V.freeze int_forward_deps
  bnRealForwardDeps <- V.freeze real_forward_deps
  return $ BayesNet { .. }


----------------------------------------------------------------------
-- * A Monad for Building Bayesian Networks
----------------------------------------------------------------------

-- | The monad for building Bayesian networks
newtype BNBuilder a =
  BNBuilder { unBNBuilder :: State PartialBayesNet a }
  deriving (Functor,Applicative,Monad)

-- | Add an integer node to the current partially-built Bayesian network
bnAddIntNode :: [GExpr BNDynRepr Prob] -> BNBuilder (GExpr BNDynRepr Int)
bnAddIntNode probs = BNBuilder $ do
  node_num <- state (insertIntNodePBN $ mkIntBayesNode probs)
  return $ intVarBNDynExpr $ BNVar BNTypeInt node_num

-- | Add a real node to the current partially-built Bayesian network
bnAddRealNode :: (BNAssign Double -> MWCRandM Double) ->
                 (GExpr BNDynRepr R -> GExpr BNDynRepr Prob) ->
                 BNBuilder (GExpr BNDynRepr R)
bnAddRealNode sampler pdf = BNBuilder $ do
  node_num <- state (insertRealNodePBN $ mkRealBayesNode sampler pdf)
  return $ realVarBNDynExpr $ BNVar BNTypeReal node_num

-- | Add a real node to the current partially-built Bayesian network
bnAddUnitNode :: GExpr BNDynRepr Prob -> BNBuilder ()
bnAddUnitNode prob = BNBuilder $ do
  void $ state (insertUnitNodePBN $ mkUnitBayesNode prob)

-- | Run a 'BNBuilder' computation to get a partial Bayesian network
runBNBuilder :: BNBuilder a -> (a, PartialBayesNet)
runBNBuilder m = runState (unBNBuilder m) emptyPBN

-- | Extract a Bayesian network from a statement of distribution type
bayesNetOf :: GStmt BNExprRepr a -> BayesNet a
bayesNetOf stmt =
  let (expr, pbn) = runBNBuilder $ unGStmt stmt in
  completeBayesNet (unGExpr expr) pbn


----------------------------------------------------------------------
-- * Bayesian Network Expressions
----------------------------------------------------------------------

-- | Bayesian network building expressions
data BNExpr a where
  BNExprDynamic :: GExpr BNDynRepr a -> BNExpr a

  BNExprBool :: Bool -> BNExpr Bool
  BNExprInt :: Int -> BNExpr Int
  BNExprDouble :: Double -> BNExpr R
  BNExprProb :: Prob -> BNExpr Prob

  BNExprFun :: (GExpr BNExprRepr a -> GExpr BNExprRepr b) -> BNExpr (a -> b)
  BNExprTuple :: TupleF ts (GExpr BNExprRepr) (ADT (TupleF ts)) ->
                 BNExpr (ADT (TupleF ts))
  BNExprADT :: (TraversableADT adt, ReifyCtorsADT adt) =>
               (adt (GExpr BNExprRepr) (ADT adt)) ->
               BNExpr (ADT adt)
  BNExprDist ::
    (GrappaData a -> BNBuilder (GExpr BNExprRepr a)) ->
    BNExpr (Dist a)

-- | Extract a dynamic probability value from a 'BNExpr' of 'Prob' type
bnExprToProb :: GExpr BNExprRepr Prob -> GExpr BNDynRepr Prob
bnExprToProb (GExpr (BNExprProb p)) = embedRepr p
bnExprToProb (GExpr (BNExprDynamic e)) = e

-- | Extract a distribution function from a 'BNExpr' of distribution type
bnExprToDist :: GExpr BNExprRepr (Dist a) ->
                GrappaData a -> BNBuilder (GExpr BNExprRepr a)
bnExprToDist (GExpr (BNExprDist f)) = f
bnExprToDist (GExpr (BNExprDynamic dyn_dist)) = noDynDist dyn_dist

-- | Convert a partially static expression to a dynamic one. This is an error at
-- the distribution type, since node-building must be static.
bnExprToDyn :: GExpr BNExprRepr a -> GExpr BNDynRepr a
bnExprToDyn (GExpr (BNExprDynamic e)) = e
bnExprToDyn (GExpr (BNExprBool b)) = embedRepr b
bnExprToDyn (GExpr (BNExprInt i)) = embedRepr i
bnExprToDyn (GExpr (BNExprDouble r)) = embedRepr r
bnExprToDyn (GExpr (BNExprProb p)) = embedRepr p
bnExprToDyn (GExpr (BNExprFun f)) =
  interp__'lam (bnExprToDyn . f . bnDynToExpr)
bnExprToDyn (GExpr (BNExprADT adt)) =
  interp__'injADT $ mapADT bnExprToDyn adt
bnExprToDyn (GExpr (BNExprTuple tup)) =
  interp__'injTuple $ mapADT bnExprToDyn tup
bnExprToDyn (GExpr (BNExprDist _)) =
  error "bnExprToDyn: distribution used in dynamic context!"

-- | Convert a dynamic expression to a partially static expression one
bnDynToExpr :: GExpr BNDynRepr a -> GExpr BNExprRepr a
bnDynToExpr = GExpr . BNExprDynamic

-- | Evaluate a real-valued 'BNExpr' relative to an assignment
evalRealBNExpr :: GExpr BNExprRepr R -> BNAssign Double -> BNDynRetReprF R
evalRealBNExpr (GExpr (BNExprDouble r)) = \_ -> r
evalRealBNExpr (GExpr (BNExprDynamic e)) = evalDynExpr e

-- | Evaluate a probability-valued 'BNExpr' relative to an assignment
evalProbBNExpr :: GExpr BNExprRepr Prob -> BNAssign Double -> BNDynRetReprF Prob
evalProbBNExpr (GExpr (BNExprProb p)) = \_ -> fromProb p
evalProbBNExpr (GExpr (BNExprDynamic e)) = evalDynExpr e

-- | Assume that a list expression has a static list structure, and extract the
-- list of expressions that it contains
bnExprToStaticList :: GExpr BNExprRepr (GList a) -> [GExpr BNExprRepr a]
bnExprToStaticList (GExpr (BNExprADT Nil)) = []
bnExprToStaticList (GExpr (BNExprADT (Cons a as'))) =
  a : bnExprToStaticList as'
bnExprToStaticList (GExpr (BNExprDynamic _)) =
  error "Not a static list!"


data BNExprRepr

instance ValidExprRepr BNExprRepr where
  type GExprRepr BNExprRepr a = BNExpr a

  interp__'bottom = bnDynToExpr interp__'bottom
  interp__'injTuple tup = GExpr $ BNExprTuple tup

  interp__'projTuple (GExpr (BNExprADT tup)) k = k tup
  interp__'projTuple (GExpr (BNExprTuple tup)) k = k tup
  interp__'projTuple (GExpr (BNExprDynamic dyn)) k =
    -- FIXME HERE: use strong projection when the return type contains 'Dist'
    bnDynToExpr $ interp__'projTuple dyn (bnExprToDyn . k . mapADT bnDynToExpr)

  interp__'app (GExpr (BNExprFun f)) arg = f arg
  interp__'app (GExpr (BNExprDynamic f)) arg =
    bnDynToExpr $ interp__'app f $ bnExprToDyn arg

  interp__'lam f = GExpr $ BNExprFun f
  interp__'fix f = f (interp__'fix f)

instance StrongTupleRepr BNExprRepr where
  interp__'strongProjTuple (GExpr (BNExprADT tup)) = tup
  interp__'strongProjTuple (GExpr (BNExprTuple tup)) = tup
  interp__'strongProjTuple (GExpr (BNExprDynamic e)) =
    mapADT (GExpr . BNExprDynamic) $ interp__'strongProjTuple e

instance ValidRepr BNExprRepr where
  type GVExprRepr BNExprRepr a = GrappaData a
  type GStmtRepr BNExprRepr a = BNBuilder (GExpr BNExprRepr a)

  interp__'projTupleStmt e k = k $ interp__'strongProjTuple e

  interp__'vInjTuple !tup =
    GVExpr (GADTData $ mapADT unGVExpr tup)
  interp__'vProjTuple (GVExpr d) k =
    matchADTGData d
    (k . mapADT GVExpr)
    (k $ mapADT (\ _ -> GVExpr GNoData) typeListProxy)

  interp__'vwild k = k (GVExpr GNoData)
  interp__'vlift (GExpr e) k = k (GVExpr $ helper e) where
    helper :: BNExpr a -> GrappaData a
    helper (BNExprDynamic _) =
      error "Cannot put a dynamic value on the left-hand side of a ~"
    helper (BNExprBool b) = GData b
    helper (BNExprInt i) = GData i
    helper (BNExprDouble d) = GData d
    helper (BNExprProb p) = GData p
    helper (BNExprFun _) =
      error "Cannot put a function on the left-hand side of a ~"
    helper (BNExprTuple tup) = GADTData $ mapADT (helper . unGExpr) tup
    helper (BNExprADT adt) = GADTData $ mapADT (helper . unGExpr) adt
    helper (BNExprDist _) =
      error "Cannot put a distribution on the left-hand side of a ~"
  -- interp__'vliftInt i k = k (GVExpr $ VData $ Id i)

  interp__'return e = GStmt (return e)
  interp__'let rhs body = body rhs
  interp__'sample d (GVExpr dv) k = GStmt $ do
    e <- bnExprToDist d dv
    unGStmt $ k e

  interp__'mkDist f = GExpr $ BNExprDist (\ dv -> unGStmt $ f $ GVExpr dv)

instance GrappaADT adt => Interp__ADT__Expr BNExprRepr adt where
  interp__'injADT adt = GExpr $ BNExprADT adt
  interp__'projADT (GExpr (BNExprADT adt)) k = k adt
  interp__'projADT (GExpr (BNExprTuple adt)) k = k adt
  interp__'projADT (GExpr (BNExprDynamic dyn)) k =
    bnDynToExpr $ interp__'projADT dyn (bnExprToDyn . k . mapADT bnDynToExpr)
  interp__'projMatchADT (GExpr (BNExprADT adt)) _ matcher k_succ k_fail =
    if (applyCtorMatcher matcher adt) then k_succ adt
    else k_fail
  interp__'projMatchADT (GExpr (BNExprTuple adt)) _ matcher k_succ k_fail =
    if (applyCtorMatcher matcher adt) then k_succ adt
    else k_fail
  interp__'projMatchADT (GExpr
                         (BNExprDynamic dyn)) ctor matcher k_succ k_fail =
    bnDynToExpr $ interp__'projMatchADT dyn ctor matcher
    (bnExprToDyn . k_succ . mapADT bnDynToExpr)
    (bnExprToDyn k_fail)

instance GrappaADT adt => Interp__ADT BNExprRepr adt where
  interp__'vInjADT adt = GVExpr (GADTData $ mapADT unGVExpr adt)
  interp__'vProjMatchADT (GVExpr d) ctor matcher k_succ k_fail =
    matchADTGData d
    (\adt ->
      if (applyCtorMatcher matcher adt) then
        k_succ $ mapADT GVExpr adt
      else k_fail)
    (k_succ $ mapADT (const $ GVExpr GNoData) ctor)

instance Interp__'source BNExprRepr a where
  interp__'source src = GVExpr <$> interpSource src

instance EmbedRepr BNExprRepr Bool where embedRepr = GExpr . BNExprBool
instance EmbedRepr BNExprRepr Int where embedRepr = GExpr . BNExprInt
instance EmbedRepr BNExprRepr R where embedRepr = GExpr . BNExprDouble
instance EmbedRepr BNExprRepr Prob where embedRepr = GExpr . BNExprProb


----------------------------------------------------------------------
-- * Expression-level Operations
----------------------------------------------------------------------

-- | Build a unary function on BN expressions from one on static values and one
-- on dynamic values
mkBnFun1 :: (IsBaseType a ~ 'True, EmbedRepr BNExprRepr b) =>
            (a -> b) -> GExpr BNDynRepr (a -> b) ->
            GExpr BNExprRepr a -> GExpr BNExprRepr b
mkBnFun1 fstatic _ (GExpr (BNExprBool x)) = embedRepr $ fstatic x
mkBnFun1 fstatic _ (GExpr (BNExprInt x)) = embedRepr $ fstatic x
mkBnFun1 fstatic _ (GExpr (BNExprDouble x)) = embedRepr $ fstatic x
mkBnFun1 fstatic _ (GExpr (BNExprProb x)) = embedRepr $ fstatic x
mkBnFun1 _ fdyn (GExpr (BNExprDynamic e)) =
  GExpr $ BNExprDynamic $ interp__'app fdyn e

-- | Build a unary function BN expression from unary functions on static and on
-- dynamic values
mkBnFunExpr1 :: (IsBaseType a ~ 'True, EmbedRepr BNExprRepr b) =>
                (a -> b) -> GExpr BNDynRepr (a -> b) ->
                GExpr BNExprRepr (a -> b)
mkBnFunExpr1 fstatic fdyn = interp__'lam $ mkBnFun1 fstatic fdyn

-- | Build a binary function on BN expressions from one on static values and one
-- on dynamic values
mkBnFun2 :: (IsBaseType a ~ 'True, IsBaseType b ~ 'True,
             EmbedRepr BNExprRepr c) =>
            (a -> b -> c) -> GExpr BNDynRepr (a -> b -> c) ->
            GExpr BNExprRepr a -> GExpr BNExprRepr b ->
            GExpr BNExprRepr c
mkBnFun2 fstatic _ (GExpr (BNExprBool b1)) (GExpr (BNExprBool b2)) =
  embedRepr $ fstatic b1 b2
mkBnFun2 fstatic _ (GExpr (BNExprInt i1)) (GExpr (BNExprInt i2)) =
  embedRepr $ fstatic i1 i2
mkBnFun2 fstatic _ (GExpr (BNExprDouble d1)) (GExpr (BNExprDouble d2)) =
  embedRepr $ fstatic d1 d2
mkBnFun2 fstatic _ (GExpr (BNExprProb p1)) (GExpr (BNExprProb p2)) =
  embedRepr $ fstatic p1 p2
mkBnFun2 _ fdyn e1 e2 =
  GExpr $ BNExprDynamic $
  interp__'app (interp__'app fdyn $ bnExprToDyn e1) $ bnExprToDyn e2

-- | Build a binary function BN expression from binary functions on static and
-- on dynamic values
mkBnFunExpr2 :: (IsBaseType a ~ 'True, IsBaseType b ~ 'True,
                 EmbedRepr BNExprRepr c) =>
                (a -> b -> c) -> GExpr BNDynRepr (a -> b -> c) ->
                GExpr BNExprRepr (a -> b -> c)
mkBnFunExpr2 fstatic fdyn =
  interp__'lam $ interp__'lam . mkBnFun2 fstatic fdyn


--
-- Boolean and comparison operations
--

instance Interp__'ifThenElse BNExprRepr where
  interp__'ifThenElse (GExpr (BNExprBool b)) t e = if b then t else e
  interp__'ifThenElse (GExpr (BNExprDynamic b)) t e =
    GExpr $ BNExprDynamic $
    interp__'ifThenElse b (bnExprToDyn t) (bnExprToDyn e)

instance Interp__'vmatchSwitch BNExprRepr where
  interp__'vmatchSwitch (GExpr (BNExprInt i)) stmts = stmts !! i
  interp__'vmatchSwitch (GExpr (BNExprDynamic _)) _ =
    error ("Bayesian networks do not support models where "
           ++ "multiple cases match the input")

instance Interp__not BNExprRepr where
  interp__not = mkBnFunExpr1 not interp__not

instance Interp__'amp'amp BNExprRepr where
  interp__'amp'amp = mkBnFunExpr2 (&&) interp__'amp'amp

instance Interp__'bar'bar BNExprRepr where
  interp__'bar'bar = mkBnFunExpr2 (||) interp__'bar'bar


instance (Eq a, Eq (BNDynRetReprF a), IsBaseType a ~ 'True,
          Interp__'eq'eq (ADHORepr VoidM BNAssign) a) =>
         Interp__'eq'eq BNExprRepr a where
  interp__'eq'eq = mkBnFunExpr2 (==) interp__'eq'eq

instance (Ord a, Ord (BNDynRetReprF a), IsBaseType a ~ 'True,
          Interp__'lt (ADHORepr VoidM BNAssign) a) =>
         Interp__'lt BNExprRepr a where
  interp__'lt = mkBnFunExpr2 (<) interp__'lt

instance (Ord a, Ord (BNDynRetReprF a), IsBaseType a ~ 'True,
          Interp__'gt (ADHORepr VoidM BNAssign) a) =>
         Interp__'gt BNExprRepr a where
  interp__'gt = mkBnFunExpr2 (>) interp__'gt

instance (Ord a, Ord (BNDynRetReprF a), IsBaseType a ~ 'True,
          Interp__'lt'eq (ADHORepr VoidM BNAssign) a) =>
         Interp__'lt'eq BNExprRepr a where
  interp__'lt'eq = mkBnFunExpr2 (<=) interp__'lt'eq

instance (Ord a, Ord (BNDynRetReprF a), IsBaseType a ~ 'True,
          Interp__'gt'eq (ADHORepr VoidM BNAssign) a) =>
         Interp__'gt'eq BNExprRepr a where
  interp__'gt'eq = mkBnFunExpr2 (>=) interp__'gt'eq

instance (Ord a, Ord (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__min (ADHORepr VoidM BNAssign) a) =>
         Interp__min BNExprRepr a where
  interp__min = mkBnFunExpr2 min interp__min

instance (Ord a, Ord (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__max (ADHORepr VoidM BNAssign) a) =>
         Interp__max BNExprRepr a where
  interp__max = mkBnFunExpr2 max interp__max


--
-- Num typeclass
--

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__'plus (ADHORepr VoidM BNAssign) a) =>
         Interp__'plus BNExprRepr a where
  interp__'plus = mkBnFunExpr2 (+) interp__'plus

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__'minus (ADHORepr VoidM BNAssign) a) =>
         Interp__'minus BNExprRepr a where
  interp__'minus = mkBnFunExpr2 (-) interp__'minus

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__'times (ADHORepr VoidM BNAssign) a) =>
         Interp__'times BNExprRepr a where
  interp__'times = mkBnFunExpr2 (*) interp__'times

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__negate (ADHORepr VoidM BNAssign) a) =>
         Interp__negate BNExprRepr a where
  interp__negate = mkBnFunExpr1 negate interp__negate

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__abs (ADHORepr VoidM BNAssign) a) =>
         Interp__abs BNExprRepr a where
  interp__abs = mkBnFunExpr1 abs interp__abs

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__signum (ADHORepr VoidM BNAssign) a) =>
         Interp__signum BNExprRepr a where
  interp__signum = mkBnFunExpr1 signum interp__signum

instance (Num a, Num (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__fromInteger (ADHORepr VoidM BNAssign) a) =>
         Interp__fromInteger BNExprRepr a where
  interp__fromInteger = mkBnFunExpr1 fromInteger interp__fromInteger

instance (Num a, EmbedRepr BNExprRepr a) =>
         Interp__'integer BNExprRepr a where
  interp__'integer i = embedRepr $ fromInteger i

instance (Num a, Num (BNDynRetReprF a),
          Eq a, Eq (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr  BNExprRepr a,
          Interp__'eqInteger (ADHORepr VoidM BNAssign) a) =>
         Interp__'eqInteger BNExprRepr a where
  interp__'eqInteger =
    mkBnFun2 (==) $ interp__'lam $ interp__'lam .  interp__'eqInteger


--
-- Fractional typeclass
--
instance (Fractional a, Fractional (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__'div (ADHORepr VoidM BNAssign) a) =>
         Interp__'div BNExprRepr a where
  interp__'div = mkBnFunExpr2 (/) interp__'div

instance (Fractional a, Fractional (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a, Interp__recip (ADHORepr VoidM BNAssign) a) =>
         Interp__recip BNExprRepr a where
  interp__recip = mkBnFunExpr1 recip interp__recip

instance (Fractional a, Fractional (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__fromRational (ADHORepr VoidM BNAssign) a) =>
         Interp__fromRational BNExprRepr a where
  interp__fromRational = mkBnFunExpr1 fromRational interp__fromRational

instance (Fractional a, EmbedRepr BNExprRepr a) =>
         Interp__'rational BNExprRepr a where
  interp__'rational r = embedRepr $ fromRational r

instance (Fractional a, Fractional (BNDynRetReprF a),
          Eq a, Eq (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr  BNExprRepr a,
          Interp__'eqRational (ADHORepr VoidM BNAssign) a) =>
         Interp__'eqRational BNExprRepr a where
  interp__'eqRational =
    mkBnFun2 (==) $ interp__'lam $ interp__'lam . interp__'eqRational


--
-- Floating typeclass
--

instance (Floating a, Floating (BNDynRetReprF a), EmbedRepr BNExprRepr a,
          Interp__pi (ADHORepr VoidM BNAssign) a) =>
         Interp__pi BNExprRepr a where
  interp__pi = embedRepr pi

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__exp (ADHORepr VoidM BNAssign) a) =>
         Interp__exp BNExprRepr a where
  interp__exp = mkBnFunExpr1 exp interp__exp

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__log (ADHORepr VoidM BNAssign) a) =>
         Interp__log BNExprRepr a where
  interp__log = mkBnFunExpr1 log interp__log

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__sqrt (ADHORepr VoidM BNAssign) a) =>
         Interp__sqrt BNExprRepr a where
  interp__sqrt = mkBnFunExpr1 sqrt interp__sqrt

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__'times'times (ADHORepr VoidM BNAssign) a) =>
         Interp__'times'times BNExprRepr a where
  interp__'times'times = mkBnFunExpr2 (**) interp__'times'times

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__logBase (ADHORepr VoidM BNAssign) a) =>
         Interp__logBase BNExprRepr a where
  interp__logBase = mkBnFunExpr2 logBase interp__logBase

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__sin (ADHORepr VoidM BNAssign) a) =>
         Interp__sin BNExprRepr a where
  interp__sin = mkBnFunExpr1 sin interp__sin

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__cos (ADHORepr VoidM BNAssign) a) =>
         Interp__cos BNExprRepr a where
  interp__cos = mkBnFunExpr1 cos interp__cos

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__tan (ADHORepr VoidM BNAssign) a) =>
         Interp__tan BNExprRepr a where
  interp__tan = mkBnFunExpr1 tan interp__tan

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__asin (ADHORepr VoidM BNAssign) a) =>
         Interp__asin BNExprRepr a where
  interp__asin = mkBnFunExpr1 asin interp__asin

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__acos (ADHORepr VoidM BNAssign) a) =>
         Interp__acos BNExprRepr a where
  interp__acos = mkBnFunExpr1 acos interp__acos

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__atan (ADHORepr VoidM BNAssign) a) =>
         Interp__atan BNExprRepr a where
  interp__atan = mkBnFunExpr1 atan interp__atan

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__sinh (ADHORepr VoidM BNAssign) a) =>
         Interp__sinh BNExprRepr a where
  interp__sinh = mkBnFunExpr1 sinh interp__sinh

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__cosh (ADHORepr VoidM BNAssign) a) =>
         Interp__cosh BNExprRepr a where
  interp__cosh = mkBnFunExpr1 cosh interp__cosh

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__tanh (ADHORepr VoidM BNAssign) a) =>
         Interp__tanh BNExprRepr a where
  interp__tanh = mkBnFunExpr1 tanh interp__tanh

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__asinh (ADHORepr VoidM BNAssign) a) =>
         Interp__asinh BNExprRepr a where
  interp__asinh = mkBnFunExpr1 asinh interp__asinh

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__acosh (ADHORepr VoidM BNAssign) a) =>
         Interp__acosh BNExprRepr a where
  interp__acosh = mkBnFunExpr1 acosh interp__acosh

instance (Floating a, Floating (BNDynRetReprF a), IsBaseType a ~ 'True,
          EmbedRepr BNExprRepr a,
          Interp__atanh (ADHORepr VoidM BNAssign) a) =>
         Interp__atanh BNExprRepr a where
  interp__atanh = mkBnFunExpr1 atanh interp__atanh


--
-- Probability expressions
--

instance Interp__realToProb BNExprRepr where
  interp__realToProb = mkBnFunExpr1 realToProb interp__realToProb

instance Interp__logRealToProb BNExprRepr where
  interp__logRealToProb = mkBnFunExpr1 logRealToProb interp__logRealToProb

instance Interp__probToReal BNExprRepr where
  interp__probToReal = mkBnFunExpr1 probToReal interp__probToReal

instance Interp__probToLogReal BNExprRepr where
  interp__probToLogReal = mkBnFunExpr1 probToLogReal interp__probToLogReal

instance Interp__gammaProb BNExprRepr where
  interp__gammaProb = mkBnFunExpr1 gammaProb interp__gammaProb


--
-- Misc expressions
--

-- NOTE: errors must be pushed into the dynamic stage, as MonoidRepr does a join
-- over all paths (including error paths!) but throws away non-MonoidRepr parts
-- of the computation...
instance Interp__gerror BNExprRepr a where
  interp__gerror = interp__'lam $ \i_expr ->
    GExpr $ BNExprDynamic $ interp__'app interp__gerror $ bnExprToDyn i_expr
    {-
    case i_expr of
      GExpr (BNExprInt i) -> gerror i
      GExpr (BNExprDynamic i) ->
        GExpr $ BNExprDynamic $ interp__'app interp__gerror i -}


----------------------------------------------------------------------
-- * Distributions
----------------------------------------------------------------------

-- | Build a real-valued distribution from a PDF defined over some subset of the
-- reals, using the supplied functions to: inject variable 'VData' from the
-- subset onto the real line; and project returned expressions in the real line
-- onto the subset.
bnSubsetDistFromPDF :: (BNAssign Double -> MWCRandM Double) ->
                       (Double -> Double) ->
                       (GExpr BNDynRepr R -> GExpr BNDynRepr R) ->
                       (GExpr BNDynRepr R -> GExpr BNDynRepr Prob) ->
                       GExpr BNExprRepr (Dist R)
bnSubsetDistFromPDF sampler toReals fromReals pdf =
  GExpr $ BNExprDist $ \dv ->
  case dv of
    GNoData ->
      (GExpr . BNExprDynamic . fromReals) <$>
      bnAddRealNode sampler (pdf . fromReals)
    GData x ->
      bnAddUnitNode (pdf $ embedRepr $ toReals x) >>
      return (GExpr $ BNExprDouble x)

-- | Build a distribution over the interval @(0,\infty)@ using a PDF defined on
-- that interval
bnPosRealsDistFromPDF :: (BNAssign Double -> MWCRandM Double) ->
                         (GExpr BNDynRepr R -> GExpr BNDynRepr Prob) ->
                         GExpr BNExprRepr (Dist R)
bnPosRealsDistFromPDF sampler =
  bnSubsetDistFromPDF sampler
  (\x ->
    -- Biject the interval (0,\infty) onto the reals via the piecewise function
    -- that maps @x@ in @(0,1)@ to @log x@ and otherwise maps @x@ to @x-1@
    if x < 1 then log x else x - 1)
  (\x ->
    -- Biject the reals onto the interval (0,\intfy) via the piecewise function
    -- that maps negative @x@ to @exp x@ and otherwise maps @x@ to @x+1@
    interp__ifLessThan x 0 (exp x) (x + 1))

-- | Build a distribution over the interval @(0,1)@ using a PDF defined on
-- that interval
bnUnitRealsDistFromPDF :: (BNAssign Double -> MWCRandM Double) ->
                          (GExpr BNDynRepr R -> GExpr BNDynRepr Prob) ->
                          GExpr BNExprRepr (Dist R)
bnUnitRealsDistFromPDF sampler =
  bnSubsetDistFromPDF sampler (toRealLbUb 0 1) (fromRealLbUb 0 1)

-- | Build a real-valued distribution from a PDF
bnDistFromPDF :: (BNAssign Double -> MWCRandM Double) ->
                 (GExpr BNDynRepr R -> GExpr BNDynRepr Prob) ->
                 GExpr BNExprRepr (Dist R)
bnDistFromPDF sampler pdf = bnSubsetDistFromPDF sampler id id pdf

-- | Build a real-valued list distribution from a list of PDFs
bnListDistFromPDFs :: [GExpr BNDynRepr R -> GExpr BNDynRepr Prob] ->
                      GExpr BNExprRepr (Dist (GList R))
bnListDistFromPDFs = error "FIXME HERE NOW: write bnListDistFromPDFs!"


instance Interp__normal BNExprRepr where
  interp__normal =
    interp__'lam $ \ mu -> interp__'lam $ \ sigma ->
    bnDistFromPDF
    (do mu_mwc <- evalRealBNExpr mu
        sigma_mwc <- evalRealBNExpr sigma
        return $ random $ MWC.normal mu_mwc sigma_mwc)
    (interp__'app interp__logRealToProb . Log.ln .
     normalDensityUnchecked (bnExprToDyn mu) (bnExprToDyn sigma))

instance Interp__uniform BNExprRepr where
  interp__uniform =
    interp__'lam $ \ lb -> interp__'lam $ \ ub ->
    bnDistFromPDF
    (do lb_mwc <- evalRealBNExpr lb
        ub_mwc <- evalRealBNExpr ub
        return $ random $ MWC.uniformR (lb_mwc, ub_mwc))
    (\x ->
      interp__ifLessThan x (bnExprToDyn lb) 0 $
      interp__ifLessThanEq (bnExprToDyn ub) x 0 $
      interp__'app interp__realToProb (x / (bnExprToDyn ub - bnExprToDyn lb)))

instance Interp__categorical BNExprRepr where
  interp__categorical =
    interp__'lam $ \ ws -> GExpr $ BNExprDist $ \dv ->
    case dv of
      GNoData ->
        (GExpr . BNExprDynamic) <$>
        bnAddIntNode (map bnExprToDyn $ bnExprToStaticList ws)
      GData i ->
        (bnAddUnitNode $ bnExprToDyn $ bnExprToStaticList ws !! i) >>
        return (GExpr $ BNExprInt i)

instance Interp__gamma BNExprRepr where
  interp__gamma =
    interp__'lam $ \ k -> interp__'lam $ \ theta ->
    bnPosRealsDistFromPDF
    (do k_mwc <- evalRealBNExpr k
        theta_mwc <- evalRealBNExpr theta
        return $ random $ MWC.gamma k_mwc theta_mwc)
    (bnExprToDyn . interp__'app interp__logRealToProb . Log.ln .
     gammaDensityUnchecked k theta . bnDynToExpr)

{-
instance Interp__beta BNExprRepr where
  interp__beta =
    interp__'lam $ \ alpha -> interp__'lam $ \ beta ->
    bnUnitRealsDistFromPDF
    (do alpha_mwc <- evalRealBNExpr alpha
        beta_mwc <- evalRealBNExpr beta
        return $ random $ MWC.beta alpha_mwc beta_mwc)
    (\x ->
      bnExprToDyn $
      interp__'app interp__logRealToProb $ Log.ln $
      betaDensityUnchecked alpha beta $ bnDynToExpr x)
-}

instance Interp__beta BNExprRepr where
  interp__beta =
    interp__'lam $ \ alpha -> interp__'lam $ \ beta ->
    bnDistFromPDF
    (do alpha_mwc <- evalRealBNExpr alpha
        beta_mwc <- evalRealBNExpr beta
        return $ random $ MWC.beta alpha_mwc beta_mwc)
    (\x ->
      let x_expr = bnDynToExpr x in
      bnExprToDyn $
      interp__ifLessThanEq x_expr 0 0 $
      interp__ifLessThanEq 1 x_expr 0 $
      interp__'app interp__logRealToProb $ Log.ln $
      betaDensityUnchecked alpha beta x_expr)

instance Interp__dirichlet BNExprRepr where
  interp__dirichlet =
    interp__'lam $ \ alphas_glist -> GExpr $ BNExprDist $ \dv_list ->
    -- We use the transformation that @xs ~ Dirichlet(alphas)@ is equivalent to
    -- @yi ~ Beta(alpha_i, sum_j>i alpha_j)@ for @i < len(alphas)@, @x0 = y0@,
    -- and @xi = yi * (1 - sum_j<i x_j)@.
    --
    -- FIXME: this currently does not marginalize over a subset of the
    -- variables, i.e., the user must supply all or none of them
    let alphas = bnExprToStaticList alphas_glist in
    case matchADTListData dv_list of
      (all isMissingGData -> True, _) ->
        do ys <-
             forM [0 .. length alphas - 2] $ \i ->
             bnExprToDist
             (interp__'app (interp__'app interp__beta (alphas !! i))
              (sum $ drop (i+1) alphas))
             GNoData
           let xs_butlast_rev =
                 foldl (\xs y_i -> (y_i * (1 - sum xs)) : xs) [] ys
           return $ glistify $ reverse $
             (1 - sum xs_butlast_rev) : xs_butlast_rev
      (matchDataList -> Just xs, _) ->
        if length xs == length alphas then
          (bnAddUnitNode $ bnExprToDyn $
           interp__'app interp__logRealToProb $ Log.ln $
           dirichletDensity alphas (map (GExpr . BNExprDouble) xs)) >>
          return (glistify $ map (GExpr . BNExprDouble) xs)
        else
          error "Wrong number of inputs to the Dirichlet distribution"
      _ ->
          error ("The Bayesian network interpretation of the Dirichlet"
                 ++ " distribution does not yet support partial data")
    where
      glistify :: [GExpr BNExprRepr a] -> GExpr BNExprRepr (GList a)
      glistify = GExpr . BNExprADT . fromHaskellListF (GExpr . BNExprADT)
      matchDataList :: [GrappaData R] -> Maybe [Double]
      matchDataList = mapM (\dv -> case dv of
                               GData x -> return x
                               GNoData -> Nothing)

{-
instance Interp__dirichlet BNExprRepr where
  interp__dirichlet =
    interp__'lam $ \ alphas_glist -> GExpr $ BNExprDist $ \dv_list ->
    -- We use the transformation that @xs ~ Dirichlet(alphas)@ is equivalent to
    -- @yi ~ Gamma(alpha_i,1)@ and @xi = yi / sum ys@.
    --
    -- FIXME: we should be able to marginalize the above relative to some
    -- supplied values --- i.e., if dv_list contains some VData elements --- by
    -- drawing the remaining xs from a Dirichlet distribution on only the
    -- relevant alphas and then scaling the result by @1 - sum vdatas@. This
    -- would make the PDF calculation more complex, though, especially if the
    -- alphas are non-static. For now, then, we require the user to supply no x
    -- values.
    do let alphas = bnExprToStaticList alphas_glist
       check_dv_list_is_params dv_list
       ys <-
         forM alphas $ \alpha ->
         bnExprToDist (interp__'app (interp__'app interp__gamma alpha) 1) VParam
       return $ GExpr $ BNExprADT $
         fromHaskellListF (GExpr . BNExprADT) $ map (/ sum ys) ys
         where
           check_dv_list_is_params :: DistVar (GList R) -> BNBuilder ()
           check_dv_list_is_params VParam = return ()
           check_dv_list_is_params (VADT Nil) = return ()
           check_dv_list_is_params (VADT (Cons VParam dvs')) =
             check_dv_list_is_params dvs'
           check_dv_list_is_params (VADT (Cons (VData _) _)) =
             error $ "The Bayesian network interpretation of the Dirichlet"
             ++ " distribution does not yet support variable data"
-}

instance Interp__ctorDist__ListF BNExprRepr where
  interp__ctorDist__Nil =
    interp__'lam $ \ mkNil -> GExpr $ BNExprDist $ \dv ->
    do _ <-
         matchADTGData dv
         (\adt -> case adt of
             Nil    -> bnExprToDist mkNil (GADTData Tuple0)
             Cons{} -> error "Unexpected Cons")
         (bnExprToDist mkNil GNoData)
       return $ GExpr $ BNExprADT Nil

  interp__ctorDist__Cons =
    interp__'lam $ \ mkCons -> GExpr $ BNExprDist $ \dv ->
    do Tuple2 hd tl <-
         interp__'strongProjTuple <$>
         matchADTGData dv
         (\adt -> case adt of
             Nil          -> error "Unexpected Nil"
             Cons hdv tlv -> bnExprToDist mkCons (GADTData (Tuple2 hdv tlv)))
         (bnExprToDist mkCons (GADTData (Tuple2 GNoData GNoData)))
       return $ GExpr $ BNExprADT $ Cons hd tl


instance Interp__adtDist__ListF BNExprRepr where
  interp__adtDist__ListF =
    interp__'lam $ \ probNil -> interp__'lam $ \ mkNil ->
    interp__'lam $ \ probCons -> interp__'lam $ \ mkCons ->
    GExpr $ BNExprDist $ \dv ->
    matchADTGData dv
    (\adt -> case adt of
        Nil ->
          bnAddUnitNode (bnExprToProb probNil) >>
          void (bnExprToDist mkNil (GADTData Tuple0)) >>
          return (GExpr $ BNExprADT Nil)
        Cons hdv tlv ->
          do bnAddUnitNode $ bnExprToProb probCons
             Tuple2 hd tl <-
               interp__'strongProjTuple <$>
               bnExprToDist mkCons (GADTData (Tuple2 hdv tlv))
             return $ GExpr $ BNExprADT $ Cons hd tl)
    (error "Bayesian networks do not support undetermined list distributions!")
