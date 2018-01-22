{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleInstances,FlexibleContexts,GADTs, ConstraintKinds, RankNTypes, TypeOperators  #-}

module Language.Grappa
       (module Language.Grappa.Distribution ,
        module Language.Grappa.Inference
       )
       where

import Language.Grappa.Distribution
import Language.Grappa.Inference
