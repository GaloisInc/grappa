
module Language.Grappa.Inference.CPrinter where

import Prelude hiding ( (<$>) )
import Text.PrettyPrint.ANSI.Leijen

import Language.Grappa.Interp.CExpr


-- | The class for C expressions, distributions, etc., that can be printed
class CPretty a where
  cpretty :: a -> Doc

instance CPretty CType where
  cpretty DoubleType = text "double"
  cpretty IntType = text "long"
  cpretty (TupleType _) = text "union value *"
  cpretty (FixedListType _ _) = text "union value *"
  cpretty (VarListType _) = text "struct var_length_array *"

size :: CType -> Int
size DoubleType = 1
size IntType = 1
size (TupleType ts) = sum $ map size ts
size (FixedListType n t) = n * size t
size (VarListType _) = 1

instance CPretty Literal where
  cpretty (DoubleLit d) = double d
  cpretty (IntLit i) = int i

instance CPretty VarName where
  cpretty (VarName n) = text $ "g_" <> show n

instance CPretty UnaryOp where
  cpretty NegateOp = text "~"
  cpretty NotOp = text "!"

instance CPretty BinaryOp where
  cpretty PlusOp = text "+"
  cpretty TimesOp = text "*"
  cpretty MinusOp = text "-"
  cpretty DivOp = text "/"
  cpretty ExpOp = text "**"
  cpretty LtOp = text "<"
  cpretty LteOp = text "<="
  cpretty GtOp = text ">"
  cpretty GteOp = text ">="
  cpretty EqOp = text "=="
  cpretty NeOp = text "!="
  cpretty AndOp = text "&&"
  cpretty OrOp = text "||"

valueArrayProj :: CExpr -> CExpr -> CType -> Doc
valueArrayProj tup off DoubleType =
  (cpretty tup) <> brackets(cpretty off) <> text ".double_value"
valueArrayProj tup off (TupleType _) =
  (text "&") <> parens(cpretty tup) <> brackets(cpretty off)

instance CPretty CExpr where
  cpretty (LitExpr l) = cpretty l
  cpretty (VarExpr v) = cpretty v
  cpretty (UnaryExpr o e) = parens((cpretty o) <> cpretty e)
  cpretty (BinaryExpr o el er) = parens((cpretty el) <+> (cpretty o) <+> cpretty er)
  --                            v ??? [type FunName = String]
  cpretty (FunCallExpr f as) = (text f) <> (tupled $ map cpretty as)
  cpretty (NamedVarExpr s) = text s
  cpretty (CondExpr t c a) = parens((cpretty t) <+> (text "?") <+> (cpretty c) <+> (text ":") <+> cpretty a)
  cpretty (TupleProjExpr ts e i) = valueArrayProj e (LitExpr $ IntLit $ sum(map size $ take i ts)) (ts !! i)
  cpretty (FixedListProjExpr t elist eix) = valueArrayProj elist (eix * LitExpr (IntLit (size t))) t
  cpretty (VarListProjExpr t elist eix) = error "FINISH.VarListProjExpr"

instance CPretty Dist where
  cpretty (DoubleDist e bs) = (cpretty e) <$> text "FINISH.DoubleDist"
  cpretty (IntDist e bs) = (cpretty e) <$> text "FINISH.IntDist"
  --                       v ???
  cpretty (TupleDist ds) = tupled(map cpretty ds)
  cpretty (FixedListDist c d) = (int c) <+> cpretty d
  cpretty (VarListDist d) = cpretty d

instance CPretty DPMix where
  cpretty dpmix = (cpretty $ clusterDist dpmix) <$> (cpretty $ valuesDist dpmix)

showDPMix :: DPMix -> String
showDPMix dpmix = show (cpretty dpmix)
