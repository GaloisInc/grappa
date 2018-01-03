{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module Language.Grappa.Inference.BayesNetInference where

import Data.Either

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VGen
import qualified Data.Vector.Mutable as MV

import qualified Numeric.Log as Log

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.ST

import Language.Grappa.Distribution
import Language.Grappa.Rand.MWCRandM
import Language.Grappa.Interp.BayesNet
import Language.Grappa.Inference.Util
import Language.Grappa.Inference.HMC

----------------------------------------------------------------------
-- * Belief Propagation
----------------------------------------------------------------------

-- | Check whether a Bayesian network contains undirected cycles in its integer
-- nodes. Note that we do not care about cycles that go through a real or unit
-- node, as the values of those remain fixed during belief propagation.
bnHasCycles :: BayesNet a -> Bool
bnHasCycles net | length (bnIntNodes net) == 0 = False
bnHasCycles net = runST $ do
  -- Perform a depth-first traversal of the forward edges
  let visit :: MV.MVector s Bool -> Int -> ExceptT () (ST s) ()
      visit visited var_ix =
        do already_visited <- MV.read visited var_ix
           if already_visited then mzero else return ()
           MV.write visited var_ix True
           mapM_ (visit visited . bnVarIndex)
             (bnIntIntForwardDeps net (mkIntVar var_ix))

  -- Initialize a vector of visited nodes to mark all nodes as unvisited, and
  -- then start at the first integer node
  visited_vec <- MV.replicate (length $ bnIntNodes net) False
  isLeft <$> runExceptT (visit visited_vec 0)

-- | A multi-dimensional array of probabilities for the different possible
-- values of a sequence of variables, represented as nested lists
data ProbArray
  = ProbArrayProb Prob
  | ProbArrayVar (BNVar Int) [ProbArray]
  deriving Show

-- | Sum all elements of a multi-dimensional probability array
sumProbArray :: ProbArray -> Prob
sumProbArray (ProbArrayProb p) = p
sumProbArray (ProbArrayVar _ sub_arrays) =
  sum $ map sumProbArray sub_arrays

-- | Marginalize a probability array by summing all elements where the given
-- variable has the given value. That is, the array represents joint
-- probabilities over @N@ variables, where @N@ is the dimension of the array and
-- where the value at multi-dimensional index @[a1,..,aN]@ represents the
-- probability that each variable @xi@ equals value @ai@, and we are computing
-- the total probability that variable @xj@ equals some value @a@.
marginalizeProbArray :: ProbArray -> BNVar Int -> Int -> Prob
marginalizeProbArray (ProbArrayProb _) _ _ = error "marginalizeProbArray"
marginalizeProbArray (ProbArrayVar var' sub_arrays) var a
  | var == var' = sumProbArray (sub_arrays !! a)
marginalizeProbArray (ProbArrayVar _ sub_arrays) var a =
  sum $ map (\arr -> marginalizeProbArray arr var a) sub_arrays

-- | Generate a probability array for all possible assignments of the given
-- variables. The function argument is used to compute the probability of a
-- given assignment, and the list of variables also specifies the cardinality of
-- each variable.
generateProbArray :: (BNIntAssign -> Prob) -> [(BNVar Int, Int)] -> ProbArray
generateProbArray getProb vars = helper emptyBNIntAssign vars where
  helper :: BNIntAssign -> [(BNVar Int, Int)] -> ProbArray
  helper accum [] = ProbArrayProb (getProb accum)
  helper accum ((var,num_vals):vars') =
    ProbArrayVar var $
    map (\val -> helper (addBNIntAssign accum var val) vars') [0 .. num_vals-1]

-- | Like 'generateProbArray' but in a monad
generateProbArrayM :: Monad m => (BNIntAssign -> m Prob) ->
                      [(BNVar Int, Int)] -> m ProbArray
generateProbArrayM getProb vars = helper emptyBNIntAssign vars where
  helper accum [] = ProbArrayProb <$> getProb accum
  helper accum ((var,num_vals):vars') =
    ProbArrayVar var <$>
    mapM (\val -> helper (addBNIntAssign accum var val) vars') [0 .. num_vals-1]

-- | An assignment of marginal probabilities to a set of integer variables
newtype Marginals = Marginals { unMarginals :: V.Vector [Prob] } deriving Show

-- | Lookup the marginal probability of a specific variable
lookupMarginal :: Marginals -> BNVar Int -> [Prob]
lookupMarginal (Marginals v) var = v V.! (bnVarIndex var)

-- | Build a initial marginal assignment for a given Bayesian network that
-- assigns probability 1 to all possible values of all variables
initialMarginals :: BayesNet a -> Marginals
initialMarginals net =
  Marginals $ V.generate (length $ bnIntNodes net)
  (flip replicate 1 . bnNodeCardinality net . mkIntVar)

-- | A monad for building and updating marginal assignments
newtype MarginalsM a =
  MarginalsM { unMarginalsM :: forall s. ReaderT (MV.MVector s [Prob]) (ST s) a }
  deriving (Functor)

instance Applicative MarginalsM where
  pure = return
  (<*>) = ap

instance Monad MarginalsM where
  return x = MarginalsM (return x)
  m >>= f = MarginalsM (unMarginalsM m >>= unMarginalsM . f)


-- | Run a 'MarginalsM' computation to modify a marginals assignment
modifyMarginals :: MarginalsM () -> Marginals -> Marginals
modifyMarginals m initMarg = runST $ do
  v <- V.thaw $ unMarginals initMarg
  runReaderT (unMarginalsM m) v
  Marginals <$> V.freeze v

-- | Lookup the marginal probability of a variable in the 'MarginalsM' monad
lookupMarginalM :: BNVar Int -> MarginalsM [Prob]
lookupMarginalM var = MarginalsM (ask >>= flip MV.read (bnVarIndex var))

-- | Multiply the existing marginals of a variable by new marginals
multiplyMarginalM :: BNVar Int -> [Prob] -> MarginalsM ()
multiplyMarginalM var new_probs =
  MarginalsM (ask >>= \v ->
               MV.modify v (zipWith (*) new_probs) (bnVarIndex var))

-- | Perform a reverse pass of belief propagation, from the leaves to the root,
-- assuming that the network is tree-structured. The result is a "suffix
-- marginal" for each integer node, assigning, to each integer node, what
-- marginal probabilities of the possible values of that node would be if we
-- took only the suffix of the network tree after that node.
reverseBeliefProp :: BayesNet a -> BNAssign Double -> Marginals
reverseBeliefProp net asgn =
  modifyMarginals process_all_nodes (initialMarginals net)
  where
    process_all_nodes :: MarginalsM ()
    process_all_nodes = 
      (mapM_ process_unit_node $ reverse $ bnUnitVars net) >>   
      (mapM_ process_int_node $ reverse $ bnIntVars net)

    process_unit_node :: BNVar () -> MarginalsM ()
    process_unit_node var =
      do let deps = bnLookupNodeIntDeps net var
             deps_with_sizes = zip deps (map (bnNodeCardinality net) deps)
             probArray =
               generateProbArray (flip (evalNodePDF net) var .
                                  flip setIntsBNAssign asgn) deps_with_sizes
         forM_ deps_with_sizes $ \(dep_var, dep_size) ->
           multiplyMarginalM dep_var $
           map (marginalizeProbArray probArray dep_var) [0 .. dep_size - 1]

    process_int_node :: BNVar Int -> MarginalsM ()
    process_int_node var =
      do let var_size = bnNodeCardinality net var
             deps = bnLookupNodeIntDeps net var
             deps_with_sizes = zip deps (map (bnNodeCardinality net) deps)
             vars_with_sizes = (var,var_size) : deps_with_sizes
         -- Get the current marginal probabilities for var
         var_probs <- lookupMarginalM var
         -- Build a probability array for all possible assignments to var and
         -- its dependencies by taking the product of var's PDF and the current
         -- estimate of its marginal probabilities
         let probArray =
               generateProbArray (evalVarMarginal var var_probs .
                                  flip setIntsBNAssign asgn) vars_with_sizes
         -- For each dependency, update its marginal probability by
         -- marginalizing it over the probability array
         forM_ deps_with_sizes $ \(dep_var, dep_size) ->
           multiplyMarginalM dep_var $
           map (marginalizeProbArray probArray dep_var) [0 .. dep_size - 1]

    -- Evaluate the product of the probability given by the PDF of a variable
    -- times an estimate of its marginal probability
    evalVarMarginal :: BNVar Int -> [Prob] -> BNAssign Double -> Prob
    evalVarMarginal var var_probs asgn' =
      (var_probs !! lookupBNAssign var asgn') * evalNodePDF net asgn' var


----------------------------------------------------------------------
-- * Sampling from a Bayes Net
----------------------------------------------------------------------

-- | Sample from the prior of a Bayes net. This does not use 'SamplingM' because
-- it is precisely one sample, not a sequence of them.
priorSample :: BayesNet a -> MWCRandM (BNAssign Double)
priorSample net =
  snd <$> runStateT (mapM sample_node $ bnTopoSorted net)
  (emptyBNAssignLen (length $ bnIntNodes net) (length $ bnRealNodes net))
  where
    -- Sample either the ith Int or jth real node
    sample_node :: SomeBNVar -> StateT (BNAssign Double) MWCRandM ()
    sample_node (SomeBNVar var@(BNVar BNTypeInt _)) =
      do asgn <- get
         i <- lift $ mwcCategorical $ evalIntNodeProbs net asgn var
         modify $ setIntBNAssign var i
    sample_node (SomeBNVar var@(BNVar BNTypeReal _)) =
      do asgn <- get
         r <- lift $ realNodeSampler (bnLookupNode net var) asgn
         modify $ setRealBNAssign var r
    sample_node (SomeBNVar (BNVar BNTypeUnit _)) = return ()

-- | Re-sample the integer nodes of a Bayesian network, by first using a reverse
-- pass of belief propagation to compute "suffix marginals" (see
-- 'reverseBeliefProp') for each variable, and then doing a forward sampling
-- pass that incorporates those marginals. This does not use 'SamplingM' because
-- it generates precisely one sample, not a sequence of them.
beliefPropSample :: BayesNet a -> BNAssign Double -> MWCRandM (BNAssign Double)
beliefPropSample net _
  | bnHasCycles net = error "beliefPropSample: cycle(s) in network"
beliefPropSample net top_asgn =
  foldM helper top_asgn (bnIntVars net)
  where
    marginals :: Marginals
    marginals = reverseBeliefProp net top_asgn

    helper :: BNAssign Double -> BNVar Int -> MWCRandM (BNAssign Double)
    helper asgn var =
      do new_val <-
           mwcCategorical $
           zipWith (*)
           (lookupMarginal marginals var)
           (evalIntNodeProbs net asgn var)
         return $ setIntBNAssign var new_val asgn

-- | Re-sample the real nodes of a Bayesian network using NUTS, and then return
-- the assignment from the last sample
nutsSample :: BayesNet a -> Int -> Int -> BNAssign Double ->
              MWCRandM (BNAssign Double)
nutsSample net num_samples num_adapt asgn =
  setAllRealsBNAssign asgn . VGen.convert <$>
  lastSamplingM (nutsda num_samples num_adapt
                 (VU.replicate (V.length $ bnRealNodes net) 1)
                 (Log.ln . fromProb . bnEvalPDF net
                  . setAllRealsBNAssign asgn . VGen.convert)
                 (VGen.convert . unBNAssignGrad .
                  bnEvalPDFGrad net . setAllRealsBNAssign asgn . VGen.convert)
                 (VGen.convert $ bnReals asgn))

-- | Iteratively re-sample the nodes of a Bayesian network, by switching between
-- using NUTS for the real-valued nodes and BP-based sampling via
-- 'beliefPropSample' for the discrete ones. As a starting point, sample from
-- the prior using 'priorSample'. The first argument gives the overall number of
-- samples to generate, each of which comes from a single cycle of NUTS followed
-- by BP-based sampling. The remaining two arguments are the two arguments given
-- to each iteration of NUTS, controlling how many steps of NUTS to perform
-- between each BP-based sampling step, and how many of those should adapt the
-- step size or epsilon parameter of NUTS.
bpNutsSample :: BayesNet a -> Int -> Int -> Int ->
                SamplingM (BNAssign Double) ()
bpNutsSample net num_samples nutsLen nutsLenAdapt =
  do init_asgn <- liftMWCRandM $ priorSample net
     go 0 init_asgn
     where
       go :: Int -> BNAssign Double -> SamplingM (BNAssign Double) ()
       go k _ | k >= num_samples = return ()
       go k asgn =
         dtrace ("bpNutsSample: go " ++ show k) $
         do asgn' <- liftMWCRandM $ nutsSample net nutsLen nutsLenAdapt asgn
            asgn_next <- liftMWCRandM $ beliefPropSample net asgn'
            go (k+1) asgn_next
