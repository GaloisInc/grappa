{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- | Support for writing inference methods, as well as some examples of
-- inference methods

module Language.Grappa.Inference
       (
       -- * External interface
         detailInferenceMethods
       , findMethod
       ) where

import qualified Data.Foldable as F
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import System.IO
import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Monad.State

import Language.Grappa.GrappaInternals
import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.DataSource
import Language.Grappa.Distribution
import Language.Grappa.Interp
import Language.Grappa.Interp.Prior
import Language.Grappa.Interp.Supply
import Language.Grappa.Interp.StandardHORepr
import Language.Grappa.Interp.SupplyJointM
import Language.Grappa.Interp.InitSupply
import Language.Grappa.Interp.UntypedAST
import Language.Grappa.Interp.BayesNet
import Language.Grappa.Interp.CRepr
import Language.Grappa.Interp.CExpr
import Language.Grappa.Interp.ProbFun
import Language.Grappa.Interp.PVIE hiding (runSamplingM)
import Language.Grappa.Rand.MWCRandM

import Language.Grappa.Inference.Util
import Language.Grappa.Inference.HMC
import Language.Grappa.Inference.GradientDescent
import Language.Grappa.Inference.BayesNetInference
import Language.Grappa.Inference.CTranslate

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VGen

--import qualified Numeric.AD.Mode.Reverse as ADR

import qualified Numeric.Log as Log

-- | Default representation for inference method parameters
type ParamRepr = StandardHORepr Identity Double Int

detailInferenceMethods :: IO ()
detailInferenceMethods = mapM_ go allMethods
  where go im =
          let header = PP.bold (PP.text (imName im)) PP.<+>
                       PP.tupled (map ppParam (imParams im))
          in PP.putDoc $ PP.vsep [ header
                                 , PP.indent 2 (PP.text (imDescription im))
                                 , PP.line
                                 ]

ppParam :: InferenceParam -> PP.Doc
ppParam ip =
  PP.hsep [ PP.text (ipName ip), PP.text "::", PP.pretty (ipType ip) ]

grappaPrint :: GrappaShow t => t -> IO ()
grappaPrint x =
  -- dtrace ("grappaPrint: " ++ grappaShow x) $
  putStrLn (grappaShow x) >> hFlush stdout

sampleDist :: ValidRepr repr => GExpr repr (Dist a) -> GVExpr repr a ->
              GStmt repr a
sampleDist d dv = interp__'sample d dv interp__'return

runPrior :: (GrappaType a,
             GrappaShow (StandardHOReprF PriorM Double Int a)) =>
            Source a -> GExpr PriorRepr (Dist a) -> IO ()
runPrior src d =
  do dv <- liftIO $ interp__'source src
     res <- runMWCRandM $ samplePrior $ sampleDist d dv
     grappaPrint res

priorMethod :: InferenceMethod
priorMethod = InferenceMethod
  { imName = "prior"
  , imDescription = "Sample from the prior"
  , imParams = []
  , imRunFunc = 'runPrior
  , imModelCopies = 1
  }

type VectorFun a = V.Vector Int -> V.Vector Double -> a

-- | Helper for inference methods using gradient information
gradHelper :: GrappaType a =>
              Source a ->
              GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
              (forall r i.
               SupplyJointCtx (VectorSupply r i) r i =>
               GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
              MWCRandM (V.Vector Int, V.Vector Double,
                        VectorFun (SJReprF (VectorSupply Double Int) a),
                        VectorFun Prob, VectorFun (V.Vector Double))
gradHelper src init_d d =
  do dv <- liftIO (interpSource src)
     let init_model = sampleDist init_d $ GVExpr $ VData dv
         model      = sampleDist d $ GVExpr $ VData dv
         mkVecFun f is rs = f (VectorSupply rs 0 is 0)
     (VectorSupply init_rs _ init_is _) <-
       initSupply init_model (VectorSupply V.empty 0 V.empty 0)
     return (init_is, init_rs,
             mkVecFun (outputOf model), mkVecFun (logProbOf model),
             logGradientOf (sampleDist d $ GVExpr $ VData dv))

runHMC :: (GrappaShow (SJReprF (VectorSupply Double Int) a), GrappaType a) =>
          GExpr ParamRepr Int -> GExpr ParamRepr Int -> GExpr ParamRepr R ->
          Source a ->
          GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
          (forall r i.
           SupplyJointCtx (VectorSupply r i) r i =>
           GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
          IO ()
runHMC (unGExpr -> len) (unGExpr -> l) (unGExpr -> e) src init_d d =
  runMWCRandM $
  do (init_is, init_rs, outF, probF, gradF) <- gradHelper src init_d d
     let m     = VU.replicate (V.length init_rs) 1
         u     = Log.ln . fromProb . probF init_is . VGen.convert
         -- FIXME: figure out how to do this without converting between boxed
         -- and unboxed vectors all the time!
         gradU = VGen.convert . gradF init_is . VGen.convert
     runSamplingM (liftIO . grappaPrint . outF init_is . VGen.convert) $
       hmc len l e m u gradU (VGen.convert init_rs)

hmcMethod :: InferenceMethod
hmcMethod = InferenceMethod
  { imName = "hmc"
  , imDescription = "Hamiltonian Monte-Carlo"
  , imParams =
      [ InferenceParam "len" "Number of samples to generate" intType
      , InferenceParam "l" "Number of simulation steps for each sample" intType
      , InferenceParam "e" "Step size for simulation steps" doubleType
      ]
  , imRunFunc = 'runHMC
  , imModelCopies = 2
  }

runHMCDA :: (GrappaShow (SJReprF (VectorSupply Double Int) a), GrappaType a) =>
            GExpr ParamRepr Int -> GExpr ParamRepr Int -> GExpr ParamRepr R ->
            Source a ->
            GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
            (forall r i.
             SupplyJointCtx (VectorSupply r i) r i =>
             GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
            IO ()
runHMCDA (unGExpr -> len) (unGExpr -> lenAdapt) (unGExpr -> lambda) src init_d d =
  runMWCRandM $
  do (init_is, init_rs, outF, probF, gradF) <- gradHelper src init_d d
     let m     = VU.replicate (V.length init_rs) 1
         u     = Log.ln . fromProb . probF init_is . VGen.convert
         -- FIXME: figure out how to do this without converting between boxed
         -- and unboxed vectors all the time!
         gradU = VGen.convert . gradF init_is . VGen.convert
     runSamplingM (liftIO . grappaPrint . outF init_is . VGen.convert) $
       hmcda len lenAdapt lambda m u gradU (VGen.convert init_rs)


hmcdaMethod :: InferenceMethod
hmcdaMethod = InferenceMethod
  { imName = "hmcda"
  , imDescription = "Hamiltonian Monte-Carlo with Dual Averaging"
  , imParams =
      [ InferenceParam "len" "Number of samples to generate" intType
      , InferenceParam "lenAdapt"
        "Number of those samples during which to adapt the step size" intType
      , InferenceParam "lambda"
        "Total path length for each sample == step size * number of steps"
        doubleType
      ]
  , imRunFunc = 'runHMCDA
  , imModelCopies = 2
  }


runNUTS :: (GrappaType a, GrappaShow (SJReprF (VectorSupply Double Int) a)) =>
           GExpr ParamRepr Int -> GExpr ParamRepr Int ->
           Source a ->
           GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
           (forall r i.
            SupplyJointCtx (VectorSupply r i) r i =>
            GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
           IO ()
runNUTS (unGExpr -> len) (unGExpr -> lenAdapt) src init_d d =
  runMWCRandM $
  do (init_is, init_rs, outF, probF, gradF) <- gradHelper src init_d d
     if V.length init_rs == 0 then
       error "nuts: no real variables to sample!"
       else return ()
     let m     = VU.replicate (V.length init_rs) 1
         u     = Log.ln . fromProb . probF init_is . VGen.convert
         -- FIXME: figure out how to do this without converting between boxed
         -- and unboxed vectors all the time!
         gradU = VGen.convert . gradF init_is . VGen.convert
     runSamplingM (liftIO . grappaPrint . outF init_is . VGen.convert) $
       nutsda len lenAdapt m u gradU (VGen.convert init_rs)


nutsMethod :: InferenceMethod
nutsMethod = InferenceMethod
  { imName = "nuts"
  , imDescription = "No U-Turn Sampling"
  , imParams =
      [ InferenceParam "len" "The number of samples to generate" intType
      , InferenceParam "lenAdapt"
        "The number of samples during which to tune/adapt the step size" intType
      ]
  , imRunFunc = 'runNUTS
  , imModelCopies = 2
  }

runBpNuts :: (GrappaShow (BNDynRetReprF a), GrappaType a) =>
             GExpr ParamRepr Int -> GExpr ParamRepr Int ->
             GExpr ParamRepr Int -> Source a -> GExpr BNExprRepr (Dist a) ->
             IO ()
runBpNuts (unGExpr -> len) (unGExpr -> nutsLen) (unGExpr -> nutsLenAdapt) src d =
  runMWCRandM $
  do dv <- liftIO (interpSource src)
     let net = bayesNetOf $ sampleDist d $ GVExpr dv
     runSamplingM (liftIO . grappaPrint . (bnEval net)) $
       bpNutsSample net len nutsLen nutsLenAdapt

bpNutsMethod :: InferenceMethod
bpNutsMethod = InferenceMethod
  { imName = "bpNuts"
  , imDescription = "Belief Propagation Sampling plus No U-Turn Sampling"
  , imParams =
      [ InferenceParam "len" "The number of samples to generate" intType
      , InferenceParam "nutsLen"
        "The number of iterations of NUTS for each sample" intType
      , InferenceParam "nutsLenAdapt"
        "The number of samples for each run of NUTS during which to tune/adapt the step size"
        intType
      ]
  , imRunFunc = 'runBpNuts
  , imModelCopies = 1
  }


runGD :: (Show (SJReprF (VectorSupply Double Int) a), GrappaType a) =>
         GExpr ParamRepr Double -> Source a ->
         GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
         (forall r i.
          SupplyJointCtx (VectorSupply r i) r i =>
          GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
         IO ()
runGD (unGExpr -> epsilon) src init_d d =
  do (init_is, init_rs, outF, probF, gradF) <-
       runMWCRandM $ gradHelper src init_d d
     let params = GdParams
           { _projectLambda = \ _ r -> r
           , _sampleLambda  = return $ V.toList init_rs
           , _evalObj       =
               return . negate . Log.ln . fromProb . probF init_is . V.fromList
           , _evalGradObj   =
               return . map negate . V.toList . gradF init_is . V.fromList
           }
     res_vec <- gd2 epsilon params
     let res = outF init_is (V.fromList res_vec)
     print res

gradientDescentMethod :: InferenceMethod
gradientDescentMethod = InferenceMethod
  { imName = "gradient_descent"
  , imDescription = "Gradient Descent"
  , imParams = [ InferenceParam "epsilon" "???" doubleType ]
  , imRunFunc = 'runGD
  , imModelCopies = 2
  }

runPython :: ToPythonDistVar a =>
             Source a -> GExpr UntypedRepr (Dist a) -> IO ()
runPython src d =
  do dv <- interp__'source src
     let model = sampleDist d dv
     printAST $ fromUntypedModel model
     putStrLn ""

pythonMethod :: InferenceMethod
pythonMethod = InferenceMethod
  { imName = "python"
  , imDescription = "Create a generic Python representation"
  , imParams = []
  , imRunFunc = 'runPython
  , imModelCopies = 1
  }

runCDPM :: HasCType a => Source a -> GExpr CRepr (Dist a) -> IO ()
runCDPM _ (GExpr d) =
  let d' = evalState (projCDist d (cType, 0)) 0 in
    renderCDist d' >> putStrLn ""

cdpmMethod :: InferenceMethod
cdpmMethod = InferenceMethod
  { imName = "cdpm"
  , imDescription = "C Dirichlet Process Mixture Model"
  , imParams = []
  , imRunFunc = 'runCDPM
  , imModelCopies = 1
  }

runPVIE :: GrappaShow (ProbFunReprF a) =>
           GExpr ProbFunRepr (VIDist a) -> Source a ->
           GExpr ProbFunRepr (Dist a) -> IO ()
runPVIE (unGExpr -> dist_expr) _ (unGExpr -> log_p) =
  pvie_main dist_expr (probToLogR . log_p)

pvieMethod :: InferenceMethod
pvieMethod = InferenceMethod
  { imName = "pvie"
  , imDescription = "Prototype Variational Inference Engine"
  , imParams =
    [ InferenceParam "dist_fam" "The distribution family to fit to the model"
      -- FIXME: make the following a nice way to write "VIDist a"
      (BaseType
       (TypeNameInfo
        { tn_th_name = ''VIDist, tn_arity = 1, tn_ctors = Nothing })
       [VarType (TVar 0)])
    ]
  , imRunFunc = 'runPVIE
  , imModelCopies = 1
  }

allMethods :: [InferenceMethod]
allMethods =
  [ priorMethod
  , hmcMethod
  , hmcdaMethod
  , nutsMethod
  , bpNutsMethod
  , gradientDescentMethod
  , pythonMethod
  , cdpmMethod
  , pvieMethod
  ]

findMethod :: Text -> Maybe InferenceMethod
findMethod n =
  F.find (\ m -> imName m == Text.unpack n) allMethods
