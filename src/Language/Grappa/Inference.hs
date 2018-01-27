{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | Support for writing inference methods, as well as some examples of
-- inference methods

module Language.Grappa.Inference
       (
       -- * External interface
         InferenceParam(..)
       , InferenceMethod(..)
       , ParamType(..)
       , detailInferenceMethods
       , findMethod
       ) where

import qualified Data.Foldable as F
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Language.Haskell.TH as TH
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import System.IO
import Control.Monad.IO.Class

import Language.Grappa.GrappaInternals
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
import Language.Grappa.Rand.MWCRandM

import Language.Grappa.Inference.Util
import Language.Grappa.Inference.HMC
import Language.Grappa.Inference.GradientDescent
import Language.Grappa.Inference.BayesNetInference

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VGen

--import qualified Numeric.AD.Mode.Reverse as ADR

import qualified Numeric.Log as Log


data ParamType = PTString | PTInt | PTFloat deriving (Eq, Show)

data InferenceParam = InferenceParam
  { ipName        :: String
  , ipDescription :: String
  , ipType        :: ParamType
  } deriving (Eq, Show)

data InferenceMethod = InferenceMethod
  { imName         :: String
  , imDescription  :: String
  , imParams       :: [InferenceParam]
  , imRunFunc      :: TH.Name
  , imModelCopies  :: Int
  } deriving (Eq, Show)

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
  PP.hsep [ PP.text (ipName ip), PP.text "::", go (ipType ip) ]
  where go PTString = PP.text "String"
        go PTInt    = PP.text "Int"
        go PTFloat  = PP.text "Float"

grappaPrint :: GrappaShow t => t -> IO ()
grappaPrint x =
  dtrace ("grappaPrint: " ++ grappaShow x) $
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
          Int -> Int -> R ->
          Source a ->
          GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
          (forall r i.
           SupplyJointCtx (VectorSupply r i) r i =>
           GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
          IO ()
runHMC len l e src init_d d =
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
      [ InferenceParam "len" "Number of samples to generate" PTInt
      , InferenceParam "l" "Number of simulation steps for each sample" PTInt
      , InferenceParam "e" "Step size for simulation steps" PTFloat
      ]
  , imRunFunc = 'runHMC
  , imModelCopies = 2
  }

runHMCDA :: (GrappaShow (SJReprF (VectorSupply Double Int) a), GrappaType a) =>
            Int -> Int -> R ->
            Source a ->
            GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
            (forall r i.
             SupplyJointCtx (VectorSupply r i) r i =>
             GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
            IO ()
runHMCDA len lenAdapt lambda src init_d d =
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
      [ InferenceParam "len" "Number of samples to generate" PTInt
      , InferenceParam "lenAdapt"
        "Number of those samples during which to adapt the step size" PTInt
      , InferenceParam "lambda"
        "Total path length for each sample == step size * number of steps"
        PTFloat
      ]
  , imRunFunc = 'runHMCDA
  , imModelCopies = 2
  }


runNUTS :: (GrappaType a, GrappaShow (SJReprF (VectorSupply Double Int) a)) =>
           Int -> Int ->
           Source a ->
           GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
           (forall r i.
            SupplyJointCtx (VectorSupply r i) r i =>
            GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
           IO ()
runNUTS len lenAdapt src init_d d =
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
      [ InferenceParam "len" "The number of samples to generate" PTInt
      , InferenceParam "lenAdapt"
        "The number of samples during which to tune/adapt the step size" PTInt
      ]
  , imRunFunc = 'runNUTS
  , imModelCopies = 2
  }

runBpNuts :: (GrappaShow (BNDynRetReprF a), GrappaType a) =>
             Int -> Int -> Int -> Source a -> GExpr BNExprRepr (Dist a) ->
             IO ()
runBpNuts len nutsLen nutsLenAdapt src d =
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
      [ InferenceParam "len" "The number of samples to generate" PTInt
      , InferenceParam "nutsLen"
        "The number of iterations of NUTS for each sample" PTInt
      , InferenceParam "nutsLenAdapt"
        "The number of samples for each run of NUTS during which to tune/adapt the step size"
        PTInt
      ]
  , imRunFunc = 'runBpNuts
  , imModelCopies = 1
  }


runGD :: (Show (SJReprF (VectorSupply Double Int) a), GrappaType a) =>
         Double -> Source a ->
         GExpr (InitSupplyRepr (VectorSupply Double Int)) (Dist a) ->
         (forall r i.
          SupplyJointCtx (VectorSupply r i) r i =>
          GExpr (SJRepr (VectorSupply r i)) (Dist a)) ->
         IO ()
runGD epsilon src init_d d =
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
  , imParams = [ InferenceParam "epsilon" "???" PTFloat ]
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

allMethods :: [InferenceMethod]
allMethods =
  [ priorMethod
  , hmcMethod
  , hmcdaMethod
  , nutsMethod
  , bpNutsMethod
  , gradientDescentMethod
  , pythonMethod
  ]

findMethod :: Text -> Maybe InferenceMethod
findMethod n =
  F.find (\ m -> imName m == Text.unpack n) allMethods
