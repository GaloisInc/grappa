{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Grappa.Inference.HMC where

import           Control.DeepSeq ( NFData, force )
import           Control.Monad ( forM )
import           Data.List ( foldl' )
import qualified Data.Vector.Unboxed as Dvu
import qualified Numeric.AD as Ad
import           System.Microtimer ( time )
import           Text.Printf ( printf )

import           Language.Grappa.Distribution
import           Language.Grappa.Rand.MWCRandM
import           Language.Grappa.Inference.Util


----------------------------------------------------------------
-- * Vectors
--
-- $vectors
--
-- Abstract vector operations and a concrete instantiation.
--
-- Conathan was not sure what kind of vectors we should use,
-- or if we should
-- keep them abstract. So, here I'm fixing a concrete vector
-- implementation, but making it clear what operations it needs to
-- provide, in case we want to refactor later.
--
-- In my bbvi implementation
-- ('Language.Grappa.Inference.VariationalInference') I used
-- @hmatrix@ ('Numeric.LinearAlgebra') vectors in most places and
-- @matrix@/@vector@ ('Data.Matrix' and 'Data.Vector') vectors when I
-- wanted to use automatic differentiation (ad). The @hmatrix@ vectors
-- won't work with ad because their elements must be a fixed numeric
-- type, whereas ad requires the vector elements to be generic with
-- constraint 'Num'. Of course, given a type that ad works with, we
-- can post compose with a mapping into the vector type used here for
-- hmc.

type V = Dvu.Vector R

vAdd :: V -> V -> V
vSub :: V -> V -> V
vScale :: R -> V -> V
vDot :: V -> V -> R
vZipWith :: (R -> R -> R) -> V -> V -> V
vZipWith3 :: (R -> R -> R -> R) -> V -> V -> V -> V
vMap :: (R -> R) -> V -> V
vMapM :: Monad m => (R -> m R) -> V -> m V

vAdd v1 v2 = Dvu.zipWith (+) v1 v2
vSub v1 v2 = Dvu.zipWith (-) v1 v2
vScale s v = Dvu.map (*s) v
vDot v1 v2 = Dvu.foldl1 (+) $ Dvu.zipWith (*) v1 v2
vZipWith op v1 v2 = Dvu.zipWith op v1 v2
vZipWith3 op v1 v2 v3 = Dvu.zipWith3 op v1 v2 v3
vMap f v = Dvu.map f v
vMapM f v = Dvu.mapM f v

vLength :: V -> Int
vLength = Dvu.length

vSum :: V -> R
vSum = Dvu.sum

vFromList :: [R] -> V
vToList :: V -> [R]
vFromList = Dvu.fromList
vToList = Dvu.toList

----------------------------------------------------------------
-- * RWMH

-- | Random Walk Metropolis Hastings.
--
-- The @propose@ parameter proposes a new value given the current
-- value. If @q' <- propose q@, then @pP q q'@ must compute the log
-- (very unnormalized, see below) probability of that proposal. The
-- @pT@ is the log (unnormalized) target density: the values returned
-- by @rwmh@ will converge to @pT@ in distribution.
--
-- Note: if the proposal distribution in symmetric, e.g. a normal
-- centered at the current value, then use @pP _ _ = 0@, since the
-- symmetric @pP@ terms in the algorithm will just cancel, and this is
-- easier than actually specifying a correct @pP@.
--
-- Note: the only property that @pP@ needs is that
--
-- @
-- exp (pP q' q) \/ exp (pP q q') =
--   Pr[propose q|at q'] \/ Pr[propose q'|at q]
-- @
--
-- The objective log probability @pT@ can be unnormalized in the usual
-- sense: we only require that
--
-- @
-- exp (pT q') \/ exp (pT q) = Pr[q'] \/ Pr[q]
-- @
--
-- w.r.t. the target distribution.
rwmh ::
  Int               {-^len: number of samples-} ->
  (V -> MWCRandM V) {-^propose: random proposal generation-} ->
  (V -> V -> R)     {-^pP: (very unnormalized) log proposal probability-} ->
  (V -> R)          {-^pT: (unnormalized) log target probability-} ->
  V                 {-^qInit: starting value-} ->
  SamplingM V ()
rwmh len propose pP pT qInit = do
  go len qInit
  where
    go ::
      Int{-^remaining number of samples-} ->
      V{-^current position-} ->
      SamplingM V ()
    go 0 _ = return ()
    go len0 q0 = do
      q1 <- liftMWCRandM $ propose q0
      q2 <- chooseNextQ q0 q1
      emitSample q2
      go (len0 - 1) q2

    -- Choose the next @q@ value using the metropolis hastings
    -- algorithm: accept the candidate @q1@ with probability
    --
    -- > min 1 ((exp (pT q1) * exp (pP q1 q0)) /
    -- >        (exp (pT q0) * exp (pP q0 q1)))
    --
    -- I.e. min of 1 and the ratio
    --
    -- > Pr[be at position q1 and propose q0]/
    -- > Pr[be at position q0 and propose q1]
    chooseNextQ q0 q1 = do
      let pt0 = pT q0
      let h0 = pt0 + pP q0 q1
      let pt1 = pT q1
      let h1 = pt1 + pP q1 q0
      randomIfLog (h1 - h0) q1 q0

-- | Run 'rwmh' and collect all the generated samples into a list
rwmh_list :: Int -> (V -> MWCRandM V) -> (V -> V -> R) ->
             (V -> R) -> V -> MWCRandM [V]
rwmh_list len propose pP pT qInit =
  listifySamplingM $ rwmh len propose pP pT qInit


----------------------------------------------------------------
-- ** Normally distributed proposals for @rwmh@.
--
-- E.g. you can do
--
-- > rwmh <len> normalPropose normalPP <log target density>
--
-- to take @<len>@ dependent samples approximately from @<log target
-- density>@.

-- | Proposal probability for 'normalPropose'. Since it's symmetric,
-- we just use a constant. See 'rwmh' docs for explanation.
normalPP :: V -> V -> R
normalPP = \_ _ -> log 1

-- | Propose new values by taking independent normals centered at old
-- values with given stddev.
normalPropose :: R -> V -> MWCRandM V
normalPropose sigma q =
  vMapM (\mu -> mwcNormal mu sigma) q

----------------------------------------------------------------
-- * HMC
--
-- $hmc
--
-- We have a variety of HMC algorithms, ordered from "hardest" to
-- "easiest" to use, in the sense of how many parameters the caller
-- must provide/tune themselves.
--
-- - 'hmc': vanilla HMC.
--
-- - 'hmcda': HMC with automatic tuning of the step size parameter,
--   epsilon.
--
-- - 'nutsda': No U-Turn Sampling: like 'hmcda', but also eliminates the
--   number-of-steps parameters from the UI, and tunes it
--   automatically on a per-proposal basis.
--
-- Note that 'rwmh' is even easier to use than 'nuts', but is expected
-- to have much worse performance in practice (in time required to
-- generate a given /quality/ of sample, not in time /per/
-- sample). But for "small" problems the performance difference may
-- not matter.
--
-- All of the HMC algorithms take a parameter @m@, the mass of the
-- particles for the Hamiltonian dynamics, which in practice give the
-- variances of the momenta samples. Making these variances correspond
-- to the variances of the target distribution is supposed to be ideal
-- -- in fact, in full generality @m@ becomes a covariance matrix, in
-- which case setting it to the covariance matrix of the target
-- distribution is ideal -- but the NUTS paper just sets it to uniform
-- @[1,...,1]@. One could approximate these covariances by simulating
-- the the target distribution using a default setting of @m@, and
-- then computing covariances for the resulting samples, but Conathan
-- has not experimented with this.
--
-- In short: for @m@ just use @[1,...,1]@ (in the dimension of the
-- target distribution, i.e. @length qInit@), if you don't know any
-- better.

-- | Hamiltonian Monte Carlo.
--
-- Generate a stream of HMC evolutions of the initial value.
--
-- The parameters:
--
-- - @len@: the length of the returned stream.
-- - @L@: the number of leap-frog steps.
-- - @e@: epsilon, the size of the leap-frog steps.
-- - @m@: the vector of masses of the momenta.
-- - @U@: the log (unnormalized) probability density of the target
--        distribution. Internally HMC samples from @x ~ exp U(x)@.
-- - @gradU@: the gradient of @U@.
-- - @qInit@: the initial value of the stream.
--
-- The point of this algorithm is that the returned stream of values
-- converge to @exp U@ in distribution as @len@ goes to infinity; this
-- lets you compute the expectation w.r.t. @exp U@ of an arbitrary
-- function @f@ by averaging the values of @f@ mapped over the stream
-- produced by hmc. The convergence depends @L@ and @e@ being chosen
-- appropriately, which is apparently a black art. The choice of @m@
-- affects the convergence rate, but a poor choice should not preclude
-- convergence all together (but what's the practical difference
-- between slow and never?). But worst of all, there's no way to know
-- if it has converged ...
--
-- If you decide you want a longer stream, just start a new hmc run
-- seeded with the final @q@ value of the previous run. You can then
-- concatenate the old and new streams.
--
-- The algorithm is described and analyzed in detail in Chapter 5 of
-- the Handbook of Markov Chain Monte Carlo:
-- http://www.mcmchandbook.net/HandbookChapter5.pdf.
hmc ::
  Int{-^len-} ->
  Int{-^L-} ->
  R{-^e-} ->
  V{-^m-} ->
  (V -> R){-^U-} ->
  (V -> V){-^gradU-} ->
  V{-^qInit-} ->
  SamplingM V ()
hmc len _L e m _U' gradU' qInit = do
  go len qInit
  where
    -- The algorithm is implemented in terms of the *negated* log
    -- density @U@. Exposing that in the interface seems confusing, so
    -- do the negation internally. We could eliminate these
    -- redefinitions, and maybe gain a little performance, by
    -- inlining them below.
    _U = negate . _U'
    gradU = vScale (-1) . gradU'

    go 0 _ = return ()
    go len0 q0 = do
      p0 <- genMomenta m
      -- Var @_L@ between 90% and 110% randomly. This is biased
      -- against the end points, e.g. suppose @_L@ is 10, then we draw
      -- uniformly from 9 to 11, but the rounding means that
      -- probability of 9 and 11 is 0.5/2, whereas probability of 10
      -- is 1/2. Could "fix" this by adding 0.5 on each end of the
      -- interval, but the implementation below is what Radford Neal
      -- had in his blog post:
      -- https://radfordneal.wordpress.com/2012/01/27/evaluation-of-nuts-more-comments-on-the-paper-by-hoffman-and-gelman/. Conathan
      -- says "fix" in quotes because the bias is just my
      -- /interpretation/ of what Neal was trying to do; I can't be
      -- sure.
      _L' <- max 1 . round <$> (genUniform (0.9 * fromIntegral _L)
                                (1.1 * fromIntegral _L))
      let (q1, p1) = evolve _L' (q0, p0)
      q2 <- chooseNextQ (q0, p0) (q1, p1)
      emitSample q2
      go (len0 - 1) q2

    -- Evolve the discritized Hamiltonian dynamics through @L@
    -- size-@e@ leap-frog steps.
    --
    -- The evolution can be optimized by combining the @2*L - 1@
    -- adjacent @e/2@ half-steps for @p@ into @L@ many @e@ full-steps.
    evolve _L' (q, p) = iterate step (q, p) !! _L'
    step = leapFrog e gradU gradK
    gradK p = vZipWith (/) p m

    -- Choose the next @q@ value, by choosing the candidate @(q1,p1)@
    -- with probability @exp (- H (q1,p1)) / exp (- H (q0,p0))@, and
    -- keeping the old value otherwise.
    chooseNextQ (q0, p0) (q1, p1) = do
      h0 <- _H (q0, p0)
      h1 <- _H (q1, p1)
      randomIfLog (h0 - h1) q1 q0
    _H (q, p) =
      let k = _K p
          u = _U q in
      -- dtrace ("q = " ++ show q ++ ", p = " ++ show p) $
      -- dtrace ("k = " ++ show k ++ ", u = " ++ show u) $
      return (k + u)
    _K p = vDot (vMap (**2) p) (vMap (0.5/) m)

-- | Run 'hmc' and collect all the generated samples into a list
hmc_list :: Int -> Int -> R -> V -> (V -> R) -> (V -> V) -> V -> MWCRandM [V]
hmc_list len _L e m _U' gradU' qInit =
  listifySamplingM $ hmc len _L e m _U' gradU' qInit


-- | HMC with Dual Averaging. Algorithm 5 from page 17 of the NUTS
-- paper.
--
-- This is a version of HMC that learns the step size, epsilon (@e@).
--
-- The code is identical with 'hmc', except for the learning epsilon
-- using 'adaptEpsilon' for the first 'lenAdapt' many steps. See
-- comments in 'hmc' to understand the duplicated code. The NUTS paper
-- using different variable names than we do here for some variables:
--
-- We use @q@ for their @theta@, @p@ for their @r@, @k@ for their @m@,
-- @len@ for their @M@, and @lenAdapt@ for their @M^{adapt}@. We use
-- @m@ for the momenta masses parameter, which they fix all equal to
-- 1.
hmcda ::
  Int{-^len-} ->
  Int{-^lenAdapt-} ->
  R{-^lambda: path length == @_L*e@ in 'hmc'-} ->
  V{-^m-} ->
  (V -> R){-^U-} ->
  (V -> V){-^gradU-} ->
  V{-^qInit-} ->
  SamplingM V ()
hmcda len lenAdapt lambda m _U' gradU' qInit = do
  e0 <- findReasonableEpsilon m _H gradU gradK qInit
  let _HBar0 = 0
  let eBar0 = 1
  let mu0 = log (10 * e0)
  go mu0 (e0,eBar0,_HBar0) 1 qInit
  where
    _U = negate . _U'
    gradU = vScale (-1) . gradU'

    -- Inner loop: repeat len times
    go _ _ k _ | k > len = return ()
    go mu (e,eBar,_HBar) k q0 = do
      -- Generate a random momentum; i.e., "kick the ball"
      p0 <- genMomenta m
      -- Calculate the number _L of simulation steps from lambda, the total
      -- simulation length, and e, the step size, and then doing a stochastic
      -- rounding of the result
      let _L = lambda / e
      _L' <- max 1 . round <$> genUniform (0.9 * _L) (1.1 * _L)
      -- Simulate for _L' steps, each of size e
      let (q1, p1) = evolve e _L' (q0, p0)
      -- Probabilistically choose between the current state q0 and the next
      -- state q1, depending on their relative probabilities; also return the
      -- ratio, alpha, of their probabilities for updating e
      (alpha,q2) <- chooseNextQ (q0, p0) (q1, p1)
      -- Update e
      let (e',eBar',_HBar') =
            if k <= lenAdapt
            then adaptEpsilon alpha defaultDelta mu
                   (fromIntegral k) (e,eBar,_HBar)
            -- For all iterations after the @lenAdapt@ adaptations, we
            -- use the last value of @eBar@ for @e@.
            else (eBar,eBar,_HBar)
      -- Emit the current sample and then recure
      emitSample q2
      go mu (e',eBar',_HBar') (k+1) q2

    evolve e _L' (q, p) =
      dtrace "evolve" $
      iterate (step e) (q, p) !! _L'
    step e = leapFrog e gradU gradK
    gradK p = vZipWith (/) p m

    chooseNextQ (q0, p0) (q1, p1) =
      let h0 = _H (q0, p0)
          h1 = _H (q1, p1)
          alpha = min 1 (exp (h0 - h1)) in
      (alpha,) <$> randomIfLog (h0 - h1) q1 q0
    _H (q, p) = _K p + _U q
    _K p = vDot (vMap (**2) p) (vMap (0.5/) m)

-- | Run 'hmcda' and collect all the generated samples into a list
hmcda_list :: Int -> Int -> R -> V -> (V -> R) -> (V -> V) -> V -> MWCRandM [V]
hmcda_list len lenAdapt lambda m _U' gradU' qInit =
  listifySamplingM $ hmcda len lenAdapt lambda m _U' gradU' qInit


-- | No U-Turn Sampling (NUTS) with Dual Averaging. Algorithm 6 on
-- page 18 of the NUTS paper.
--
-- This is a version of HMC that learns the step size, epsilon (@e@),
-- and the number-of-steps (@L@), automatically. More precisely, the
-- number-of-steps is not fixed, and rather when generating each
-- proposal, the Hamiltonian dynamics are evolved until a "U-turn" is
-- encountered. In order to preserve various technical properties
-- required to prove correctness of the NUTS algorithm, the definition
-- of "U-turn" is a little complicated.
--
-- Note that are variable names correspond to the HMC chapter in the
-- MCMC Handbook, not the NUTS paper that this algorithm comes
-- from. The translations from our names to their names are:
--
-- > Us       -> Them
-- > =======================
-- > lenAdapt -> M^{adapt}
-- > len      -> M
-- > U        -> -\mathcal{L} -- We negate to get "energy".
-- > qInit    -> \Theta^0
-- > q        -> \Theta
-- > p        -> r
-- > k        -> m
-- > m        -> [1,...,1]    -- They use unit mass for all momenta.
--
-- The algorithm in the paper also takes a @delta@ param, but we just
-- fix it to 'defaultDelta' internally.
nutsda ::
  Int{-^len: total number of samples, including learning-} ->
  Int{-^lenAdapt: number of learning-phase samples-} ->
  V{-^m: momenta masses/variances-} ->
  (V -> R){-^U: log density of target distribution-} ->
  (V -> V){-^gradU: gradient of U-} ->
  V{-^qInit: initial sample value-} ->
  SamplingM V ()
nutsda len lenAdapt m _U' gradU' qInit = do
  !e0 <- findReasonableEpsilon m _H gradU gradK qInit
  let _HBar0 = 0
  let eBar0 = 1
  let mu0 = log (10 * e0)
  go mu0 (e0,eBar0,_HBar0) 1 qInit
  where
    _U = negate . _U'
    gradU = vScale (-1) . gradU'

    go :: R -> (R,R,R) -> Int -> V -> SamplingM V ()
    go _ _ k _ | k > len = return ()
    go mu (e,eBar,_HBar) k q0 = dtrace ("NUTS: go (q0 = " ++ show q0 ++ ")") $ do
      -- Choose a random "direction" q0
      p0 <- genMomenta m
      let _logpr0 = logPr (q0,p0)
      let logpr0 = dtrace ("NUTS: logpr0 = " ++ show _logpr0) _logpr0
      -- Generate a "slice variable" u, which acts as a lower cutoff on the
      -- probabilities of candidates we might choose to evolve to (note that the
      -- current position always has greater probability than u)
      --
      -- u <- genUniform 0 (exp logpr0)
      --
      -- NOTE: we sample u in log space, to deal with the case when logpr0 gets
      -- small, using the following chain of equivalences:
      --
      -- u ~ Uniform(0,ub) iff
      -- x ~ StdUniform, u = x * ub  iff
      -- y ~ Exp(1), x = exp (-y), u = x * ub  iff
      -- y ~ Exp(1), log u = log ub - y
      y <- genExponential 1
      let log_u = logpr0 - y

      -- Initialize the iteration variables use by the inner loop
      let qMinus = q0
          qPlus  = q0
          pMinus = p0
          pPlus  = p0
          j      = 0
          q1     = q0
          n      = 1
      -- Execute the inner NUTS loop, building a tree of candidates and choosing
      -- one of them, returning also the total, alpha, of all MH acceptance
      -- ratios and the number, n_alpha, of ratios we added for this sum
      (q1, alpha, n_alpha) <-
        evolve log_u e qMinus qPlus pMinus pPlus j q1 n (q0, p0)
      -- Adapt e, if appropriate
      let (e',eBar',_HBar') =
            dtrace ("adaptEpsilon: alpha = " ++ show alpha
                    ++ ", n_alpha = " ++ show n_alpha) $
            if k <= lenAdapt
            then adaptEpsilon (alpha / n_alpha) defaultDelta mu
                   (fromIntegral k) (e,eBar,_HBar)
            -- For all iterations after the @lenAdapt@ adaptations, we
            -- use the last value of @eBar@ for @e@.
            else (eBar,eBar,_HBar)
      -- Emit the current sample and recurse!
      emitSample q1
      go mu (e',eBar',_HBar') (k+1) q1

    -- The main inner loop of NUTS, where we iteratively build up a tree of
    -- candidate states to transition to, for the next iteration of the outer
    -- loop. Only some of these candidate states are "valid": their probability
    -- must be at least equal to the "splitting variable" u. (Note that the
    -- initial state always has probability greater than u.) On the jth
    -- iteration, we build up a tree of size 2^j, by doubling the tree of the
    -- last iteration. This doubling could be either in the forward direction,
    -- finding the next 2^(j-1) states of Hamiltonian simulation after the last
    -- state in the tree, or in the backward direction, running the simulation
    -- in reverse from the first state in the tree. In order that we do not have
    -- to store all 2^j states, however, the algorithm only maintains the
    -- "forward-most" state (qPlus,pPlus), the "backward-most" state
    -- (qMinus,pMinus), and the currently chosen candidate q1, which must be
    -- valid, for the next state we are currently planning to transition
    -- to. (When we transition, the momentum p1 is thrown away, so no need to
    -- keep it around.) The reason to sometimes simulate backwards has to do
    -- with the reversability condition of MCMC samplers, which is required to
    -- make sure that our generated samples truly approximate the posterior
    -- distribution. This inner loop terminates when either: the error in
    -- simulation has gotten bigger than _deltaMax; or a "U-turn" is detected,
    -- where the momentum pPlus or pMinus associated with one of the
    -- forward-most or backward-most states points back towards the other.
    --
    evolve ::
      R -> R -> V -> V -> V -> V -> Int -> V -> R -> (V, V) ->
      SamplingM V (V, R, R)
    evolve log_u e qMinus qPlus pMinus pPlus j q1 n (q0, p0) =
      dtrace ("evolve: j = " ++ show j ++ ", q1 = " ++ show q1) $ do

      -- Pick a direction (forwards == 1 or backwards == -1) to grow the tree
      v_j <- genNegativeOneOrOne

      -- Build the tree one step in the chosen direction, returning: the new
      -- extreme states; the current candidate q1 for the next state to
      -- transition to; the number of "valid" states n' in the tree we have
      -- built so far; whether we have reached a stopping condition (indicated
      -- by s' = 1); the total of the MH acceptance ratios of all states, valid
      -- or not; and the number of states in the tree (which could be < 2^j if
      -- we reached a stopping condition)
      (qMinus,pMinus,qPlus,pPlus,q',n',s',alpha,n_alpha) <-
        if v_j == (-1)
        then do
          (qMinus,pMinus,_,_,q',n',s',alpha,n_alpha) <-
             buildTree qMinus pMinus log_u v_j j e (q0, p0)
          return (qMinus,pMinus,qPlus,pPlus,q',n',s',alpha,n_alpha)
        else do
          (_,_,qPlus,pPlus,q',n',s',alpha,n_alpha) <-
             buildTree qPlus pPlus log_u v_j j e (q0, p0)
          return (qMinus,pMinus,qPlus,pPlus,q',n',s',alpha,n_alpha)

      -- Pick the new "chosen" state from the latest iteration of building the
      -- tree, unless: the latest iteration hit a stop condition, in which case
      -- we never choose the new chosen state; or the number of "valid" states
      -- in the new tree iteration n' is smaller than the old number of "valid"
      -- states, in which case we transition with probability n' / n. This is,
      -- intuitively, like a sequence of MH transitions, from one set of valid
      -- candidates to the next.
      q1 <-
        dtrace ("q' = " ++ show q' ++ ", n' = " ++ show n'
                ++ ", n = " ++ show n) $
        if s' then randomIf (min 1 (n'/n)) q' q1 else return q1

      -- Update the number of "valid" candidates, the stopping condition, and
      -- the tree size exponent j
      n <- return $ n + n'
      s <- return $ s' && noUTurn qPlus qMinus pPlus pMinus
      j <- return $ j + 1

      -- Stop if it is time to stop, otherwise recurse
      if s then evolve log_u e qMinus qPlus pMinus pPlus j q1 n (q0, p0)
        else return (q1, alpha, n_alpha)

    -- | Choose -1 or 1 with equal probability.
    genNegativeOneOrOne = do
      x <- genUniform (-1) 1
      return $ if x >= 0 then 1 else -1

    buildTree q p log_u v j e (q0, p0)
      | j == 0 = do
          let (q', p') = step (fromInteger v * e) (q, p)
          let logpr' = logPr (q',p')
          let logpr0 = logPr (q0,p0)
          -- let n' = indicator $ u <= exp logpr'
          -- let s' = u <= exp (_DeltaMax + logpr')
          let n' = indicator $ log_u <= logpr'
          let s' = log_u < _DeltaMax + logpr'
          let alpha = min 1 (exp $ logpr' - logpr0)
          if isNaN alpha then
            error ("NUTS: alpha is a NaN! (logpr0 = "
                   ++ show logpr0 ++ ", logpr' = " ++ show logpr' ++ ")")
            else
            dtrace ("buildTree: j = 0, q' = " ++ show q'
                    ++ ", logpr' = " ++ show logpr' ++ ", n' = " ++ show n'
                    ++ ", log_u =" ++ show log_u) $
            return (q',p',q',p',q',n',s',alpha,1)
      | otherwise = do
          (qMinus,pMinus,qPlus,pPlus,q',n',s',alpha',n_alpha') <-
            buildTree q p log_u v (j-1) e (q0, p0)
          if s'
            then do
            (qMinus,pMinus,qPlus,pPlus,q'',n'',s'',alpha'',n_alpha'') <-
              if v == (-1)
              then do
                (qMinus,pMinus,_,_,q'',n'',s'',alpha'',n_alpha'') <-
                  buildTree qMinus pMinus log_u v (j-1) e (q0,p0)
                return (qMinus,pMinus,qPlus,pPlus,q'',n'',s'',alpha'',n_alpha'')
              else do
                (_,_,qPlus,pPlus,q'',n'',s'',alpha'',n_alpha'') <-
                  buildTree qPlus pPlus log_u v (j-1) e (q0,p0)
                return (qMinus,pMinus,qPlus,pPlus,q'',n'',s'',alpha'',n_alpha'')
            q' <-
              dtrace ("buildTree: j = " ++ show j
                      ++ ", q' = " ++ show q' ++ ", q'' = " ++ show q''
                      ++ ", n' = " ++ show n' ++ ", n'' = " ++ show n'') $
              if n' + n'' == 0 then
                -- It doesn't matter in this case which of q' and q'' we choose,
                -- because we won't pick anything in this subtree anyway as the
                -- total n will be 0
                return q'
              else
                randomIf (n'' / (n' + n'')) q'' q'
            alpha' <- return $ alpha' + alpha''
            n_alpha' <- return $ n_alpha' + n_alpha''
            s' <- return $ s'' && noUTurn qPlus qMinus pPlus pMinus
            n' <- return $ n' + n''
            return (qMinus,pMinus,qPlus,pPlus,q',n',s',alpha',n_alpha')
            else
            return (qMinus,pMinus,qPlus,pPlus,q',n',s',alpha',n_alpha')

    -- Check for U-turns.
    --
    -- Note that all vectors are "forward" oriented: if @p0@ is the
    -- initial position, the forward moves are evolved with a
    -- /positive/ step size in @p0@ direction, and backwards moves
    -- are evolved with a /negative/ step size, but still in the
    -- @p0@ direction. Contrast this with the other implementation
    -- choice, which would evolve in the @- p0@ direction using a
    -- positive step size. This choice of keeping everything forward
    -- oriented is why we check
    --
    -- > (qPlus `vSub` qMinus) `vDot` pMinus
    --
    -- and not
    --
    -- > (qMinus `vSub` qPlus) `vDot` pMinus
    --
    -- when checking for U-turns in the backwards direction.
    noUTurn qPlus qMinus pPlus pMinus =
      ((qPlus `vSub` qMinus) `vDot` pMinus) >= 0 &&
      ((qPlus `vSub` qMinus) `vDot` pPlus) >= 0

    -- Recommendation from NUTS paper page 9.
    _DeltaMax = 1000

    step e = leapFrog e gradU gradK
    gradK p = vZipWith (/) p m

    _H (q, p) = _K p + _U q
    _K p = vDot (vMap (**2) p) (vMap (0.5/) m)
    logPr (q, p) = negate $ _H (q, p)


-- | Run 'nutsda' and collect all the generated samples into a list
nutsda_list :: Int -> Int -> V -> (V -> R) -> (V -> V) -> V -> MWCRandM [V]
nutsda_list len lenAdapt m _U' gradU' qInit =
  listifySamplingM $ nutsda len lenAdapt m _U' gradU' qInit


-- | The @if-else@ part of Algorithm 5 on page 17 of the NUTS paper.
--
-- Also part of Algorithm 6 on page 18, with a different convention in the
-- caller for @alpha@.
--
-- The paper uses the variable name @m@ where we use @k@ here, since our
-- variable names correspond to the HMC chapter in the MCMC Handbook, and so we
-- use @m@ for the momenta mass vector.
--
-- The idea of this algorithm is to continually update the step size @e@ to
-- maintain a target Metropolis-Hastings acceptance ratio @delta@, where @alpha@
-- is the current acceptance ratio, @k@ is the iteration number, and @_HBar@ is
-- a weighted running sum of how far off we were, equal to
--
-- sum (i = 1 .. k) of (1 / k + t0) (delta - alpha_i)
--
-- Note that @1 - 1/(k+t0) == (k-1 + t0) / (k + t0)@, so the _HBar' calculation
-- computes the above sum. The @t0@ term effectively starts @t@ off at a value
-- greater than @1@, to increase stability. The @mu@ parameter is the value that
-- we are shrinking the estimates of the log of @e@ towards, modulo changes in
-- @_HBar@, and @gamma@ is a rate parameter that controls this shrinkage. The
-- @eBar@ value is another running weighted average of returned @e@ terms, that
-- should also converge over time to @sum_i 1/k (delta - alpha_i)@, and is the
-- step size @e@ that we switch to when we are done adapting @e@. This is the
-- "dual averaging", since @eBar@ is a second running weighted average... at
-- least, as far as I understand it.
--
adaptEpsilon ::
  R -> R -> R -> R -> (R, R, R) -> (R, R, R)
adaptEpsilon alpha delta mu k (_,eBar,_HBar) =
  (e',eBar',_HBar')
  where
    _HBar' = (1 - 1/(k+t0))*_HBar + (1/(k+t0))*(delta - alpha)
    logE' = mu - (sqrt k/gamma)*_HBar
    logEBar' = k**(-kappa) * logE' + (1 - k**(-kappa))*log eBar
    e' = exp logE'
    eBar' = exp logEBar'

    gamma = 0.05
    t0 = 10
    kappa = 0.75

-- | The target acceptance ratio, for calling 'adaptEpsilon'.
--
-- On page 16 of the NUTS paper it says that under "fairly strong"
-- assumptions, the optimal value for delta is 0.65. Conathan didn't
-- look into what those assumptions were, and I have no intuition for
-- setting this parameter to a different value.
defaultDelta :: R
defaultDelta = 0.65

-- | Generate a momenta vector @p@ with the given masses (variances).
genMomenta :: V -> SamplingM V V
genMomenta m = vMapM (genNormal 0) m

-- | One step of the leapfrog discritization of the Hamiltonian dynamics.
--
-- In regular HMC this function is iterated, and so a possible optimization is
-- to collapse the inner half-steps of @p@. See comments in 'hmc'
-- implementation.
leapFrog :: R -> (V -> V) -> (V -> V) -> (V, V) -> (V, V)
leapFrog e gradU gradK (q0, p0) =
  dtrace ("leapFrog: stepping from " ++ show (q0,p0) ++ " to " ++ show (q1,p2)) $
  dtrace ("e = " ++ show e ++ ", gradU = " ++ show (gradU q0)) $
  (q1, p2) where
  grad0 = gradU q0
  p1 = p0 `vAdd` vScale (-e/2) grad0
  q1 = q0 `vAdd` vScale e (gradK p1)
  grad1 = gradU q1
  -- Note that next step starts by subtracting @(-e/2) (gradU q1)@ again!
  p2 = p1 `vAdd` vScale (-e/2) grad1

-- | Nuts paper Algorithm 4 on page 17.
--
-- We use @q@ for @theta@ and @p@ for @r@.
findReasonableEpsilon ::
  V -> ((V, V) -> R) -> (V -> V) -> (V -> V) -> V -> SamplingM V R
findReasonableEpsilon m _H gradU gradK q = do
  -- First, perform one step of Hamiltonian simulation in a random direction
  let e0 = 1
  p <- genMomenta m
  let qp = (q,p)
      qp' = leapFrog e0 gradU gradK qp
      lograt = logPrRatio qp' qp
  -- If the resulting state qp' has a close enough probability to the initial
  -- state qp, meaning qp' / qp is close to 1 (> 0.5), then we can choose a
  -- bigger epsilon, by setting a = 1; otherwise we need to shrink epsilon, and
  -- we choose a = -1
  let a = 2 * indicator (lograt > log 0.5) - 1
  return $ go a qp e0 qp'
  where
    -- Return @log (Pr qp' / Pr qp)@. Because @Pr qp = exp (- _H qp)@,
    -- we subtract the numerator energy.
    logPrRatio qp' qp = _H qp - _H qp'
    -- Repeatedly grow (if a=1) or shrink (if a=-1) epsilon, while it remains
    -- "reasonable"
    go a qp e qp' =
      let lograt = logPrRatio qp' qp in
      if a * lograt <= (-a) * log 2 then e else
        let e' = 2**a * e
            qp'' = leapFrog e' gradU gradK qp in
        go a qp e' qp''

indicator :: Num a => Bool -> a
indicator b = if b then 1 else 0

----------------------------------------------------------------
-- * Tests
--
-- $tests
-- To test hmc we use hmc to approximate some known expectations.
--
-- The next test, after 'testNormal', could be the test from Radford
-- Neal's blog:
-- https://radfordneal.wordpress.com/2012/01/27/evaluation-of-nuts-more-comments-on-the-paper-by-hoffman-and-gelman/.

-- | Time an IO computation, including the time needed to fully
-- evaluate the result.
timeForced :: NFData a => IO a -> IO (Double, a)
timeForced x = time $ do
  !r <- force <$> x
  return r

-- | Normal/Gaussian test.
--
-- This test is a success if the ell_2 error is small.
--
-- Seems to do well with at least 10000 samples, if the mean and
-- especially stddev are small. Might be useful to experiment with
-- different @_L@, @e@, and @m@ values inside the test, and augment
-- @hmc@ to print its acceptance rate (proportion of new proposals
-- that are accepted).
--
-- The samples generated during adaptation are discarded.
--
-- The first triple is for HMC, and the second is for HMCDA.
testNormal ::
  Int{-^lenAdapt: number of samples-} ->
  Int{-^len: number of epsilon adaptation steps for 'hmcda' and 'nutsda'-} ->
  R{-^mu: target mean-} ->
  R{-^sigma: target stddev-} ->
  IO [(String,R,R,R)]{-^\[(alg, sample mean, sample stddev, ell_2 error)\]-}
testNormal lenAdapt len mu sigma = do
  -- Partially apply the HMC algorithms until they have a common
  -- interface.
  printf "%-6s: %-6s %-6s %-6s time\n" "alg" "mu" "sigma" "error"
  printf "==================================\n"
  forM [ ("rwmh", \_ pT _ qInit' ->
             rwmh_list len (normalPropose 1) normalPP pT qInit')
       , ("hmc", hmc_list len _L e)
       , ("hmcda", hmcda_list len lenAdapt lambda)
       , ("nutsda", nutsda_list len lenAdapt)
       ] $ \(name, h) -> do
    (dt, samples) <- timeForced $
      (drop lenAdapt <$>) . runMWCRandM $
        h m (_U . vToList) (vFromList . gradU . vToList) qInit
    let samples' = concatMap vToList samples
    let mean = sampleMean samples'
    let variance = sampleVariance samples'
    let stddev = variance**0.5
    let err = ((mu - mean)**2 + (sigma - stddev)**2)**0.5
    let [sMean,sStddev,sErr::String] =
          map (printf "%.0e") [mean,stddev,err]
    printf "%-6s: %-6s %-6s %-6s %.3f\n" name sMean sStddev sErr dt
    return (name,mean,stddev,err)
  where
    lambda = fromIntegral _L * e
    _L = 20
    e = 0.3
    m = vFromList [1]
    qInit = vFromList [0]
    -- Recall that the pdf we give the log of here need not be
    -- normalized; this one is not: we dropped the
    -- @sqrt (2 sigma**2 pi)@ factor.
    _U :: Floating a => [a] -> a
    _U [x] = negate $ (x - toFloating mu)**2 /
                      (2 * (toFloating sigma)**2)
    _U _ = error "_U: bad arg"
    -- Is there a simpler way to do this cast?
    toFloating :: (Real a, Floating b) => a -> b
    toFloating = fromRational . toRational
    gradU :: [R] -> [R]
    gradU [x] = Ad.grad _U [x]
    gradU _ = error "gradU: bad arg"
    sampleMoment k samples = sum (map (**k) samples) /
                             fromIntegral (length samples)
    sampleMean samples = sampleMoment 1 samples
    sampleVariance samples = sampleMoment 2 samples - (sampleMean samples)**2

-- | The example from Radford Neal's blog post on NUTS evaluation.
--
-- See
-- https://radfordneal.wordpress.com/2012/01/27/evaluation-of-nuts-more-comments-on-the-paper-by-hoffman-and-gelman/.
--
-- I've only implemented the distribution he used -- a 30 variable
-- independent normal with standard deviations
--
-- > [110,100]++[16,16-(16-8)/25..8]++[1.1,1]
--
-- which he says is a better test than choosing random std devs -- and
-- not the sample variance test by binning the samples into groups and
-- comparing their variances. But it might be good to implement the
-- binning part of the test as well.
--
-- Instead of binning, I'm just computing the means and variances of
-- the components of the sample, and comparing them to the expected
-- means and variances, like in the single var 'testNormal' above.
--
-- Unlike 'testNormal', this test using pure vector operations and
-- does not use 'AD', so it should be relatively fast.
testMVNormal ::
  Int{-^lenAdapt: number of samples-} ->
  Int{-^len: number of epsilon adaptation steps for 'hmcda' and 'nutsda'-} ->
  R{-^mu: target mean for all vars-} ->
  IO [(String,V,V,R)]{-^\[(alg, sample means, sample stddevs, ell_2 error)\]-}
testMVNormal lenAdapt len mu = do
  -- Partially apply the HMC algorithms until they have a common
  -- interface.
  printf "%-6s: %-6s time\n" "alg" "error"
  printf "==================================\n"
  forM [("rwmh", \_ pT _ qInit' ->
            rwmh_list len (normalPropose 1) normalPP pT qInit')
       , ("hmc", hmc_list len _L e)
       , ("hmcda", hmcda_list len lenAdapt lambda)
       , ("nutsda", nutsda_list len lenAdapt)
       ] $ \(name, h) -> do
    (dt, samples) <- timeForced $
      (drop lenAdapt <$>) . runMWCRandM $ h m _U gradU qInit
    let means = sampleMeans samples
    let variances = sampleVariances samples
    let stddevs = vMap (**0.5) variances
    let err = ((vSum . vMap (**2) $ (means `vSub` mus)) +
               (vSum . vMap (**2) $ (stddevs `vSub` sigmas)))**0.5
    let [sErr::String] =
          map (printf "%.0e") [err]
    printf "%-6s: %-6s %07.3f\n" name sErr dt
    return (name,means,stddevs,err)
  where
    m = vFromList . replicate 30 $ 1
    mus = vFromList . replicate 30 $ mu
    sigmas = vFromList $ [110,100]++[16,16-(16-8)/25..8]++[1.1,1]
    lambda | vLength sigmas == 30 = fromIntegral _L * e
           | otherwise = error "BUG: conathan can't count!"
    _L = 20
    e = 0.3
    qInit = vZero
    vZero = vFromList . replicate 30 $ 0

    -- Recall that the pdf we give the log of here need not be
    -- normalized; this one is not: we dropped the
    -- @sqrt (2 sigma**2 pi)@ factors.
    _U :: V -> R
    _U q = vSum $ vZipWith3
      (\x m' s -> negate $ (x - m')**2 / (2 * s**2))
      q mus sigmas
    gradU :: V -> V
    gradU q = vZipWith3
      (\x m' s -> 2*(m' - x) / (2 * s**2))
      q mus sigmas

    moments k vs =
      (1 / fromIntegral (length vs)) `vScale`
      (foldl' (\sum' v -> sum' `vAdd` vMap (**k) v) vZero vs)
    sampleMeans samples = moments 1 samples
    sampleVariances samples = moments 2 samples `vSub`
                              vMap (**2) (sampleMeans samples)
