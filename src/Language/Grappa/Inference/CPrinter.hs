
module Language.Grappa.Inference.CPrinter where

import Text.PrettyPrint.ANSI.Leijen

import Language.Grappa.Interp.CExpr


-- | The class for C expressions, distributions, etc., that can be printed
class CPretty a where
  cpretty :: a -> Doc

instance CPretty DPMix where
  cpretty dpmix =
    error "FIXME!"

showDPMix :: DPMix -> String
showDPMix dpmix = show (cpretty dpmix)
