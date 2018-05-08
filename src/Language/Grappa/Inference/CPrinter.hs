
module Language.Grappa.Inference.CPrinter where

import Prelude hiding ( (<$>) )
import Text.PrettyPrint.ANSI.Leijen
import GHC.IO.Handle.FD

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
  cpretty NegateOp = char '~'
  cpretty NotOp = char '!'

instance CPretty BinaryOp where
  cpretty PlusOp = char '+'
  cpretty TimesOp = char '*'
  cpretty MinusOp = char '-'
  cpretty DivOp = char '/'
  cpretty ExpOp = text "**"
  cpretty LtOp = char '<'
  cpretty LteOp = text "<="
  cpretty GtOp = char '>'
  cpretty GteOp = text ">="
  cpretty EqOp = text "=="
  cpretty NeOp = text "!="
  cpretty AndOp = text "&&"
  cpretty OrOp = text "||"

valueArrayProj :: CExpr -> CExpr -> CType -> Doc
valueArrayProj tup off DoubleType =
  (cpretty tup) <> brackets(cpretty off) <> text ".double_value"
valueArrayProj tup off (TupleType _) =
  (char '&') <> parens(cpretty tup) <> brackets(cpretty off)

instance CPretty CExpr where
  cpretty (LitExpr l) = cpretty l
  cpretty (VarExpr v) = cpretty v
  cpretty (UnaryExpr o e) = parens((cpretty o) <> cpretty e)
  cpretty (BinaryExpr o el er) = parens((cpretty el) <+> (cpretty o) <+> cpretty er)
  cpretty (FunCallExpr f as) = (text f) <> (tupled $ map cpretty as)
  cpretty (NamedVarExpr s) = text s
  cpretty (CondExpr t c a) = parens((cpretty t) <+> (char '?') <+> (cpretty c) <+> (char ':') <+> cpretty a)
  cpretty (TupleProjExpr ts e i) = valueArrayProj e (LitExpr $ IntLit $ sum(map size $ take i ts)) (ts !! i)
  cpretty (FixedListProjExpr t elist eix) = valueArrayProj elist (eix * LitExpr (IntLit (size t))) t
  cpretty (VarListProjExpr t elist eix) = error "FINISH.VarListProjExpr"

instance CPretty Dist where
  cpretty (DoubleDist e bs) = (cpretty e)
  cpretty (IntDist e bs) = (cpretty e)
  cpretty (TupleDist ds) = cat $ punctuate (space <> (char '+') <> space) (map cpretty ds)
  cpretty (FixedListDist c d) = (int c) <+> cpretty d
  cpretty (VarListDist d) = cpretty d

mkVar :: String -> Int -> String
mkVar s i = s ++ (show i)

-- pred types, last type, name prefix
varNames :: [CType] -> CType -> String -> [String]
varNames ts f p =
  let l = length ts in
  concat [map (\n -> p ++ (show n)) [0..l-2], [p ++ show (l-1)]]

-- [(type, name)]
mkDecls :: [(CType,String)] -> [Doc]
mkDecls ds = map (\t -> (cpretty $ fst t) <+> text (snd t)) ds

-- pred types, last type
varDecls :: [CType] -> CType -> Doc
varDecls ts f = encloseSep lparen rparen (comma <> space) (mkDecls (zip ts (varNames ts f "x")))

-- body
mkBody :: Doc -> Doc
mkBody b = lbrace <$> (indent 4 ((text "return") <+> b <> semi)) <> line <> rbrace <> line

-- fn name, decls, body
mkDistFunc :: String -> Doc -> Doc -> Doc
mkDistFunc f ds b = (text "double") <+> text("pdf_" ++ f) <+> ds <+> mkBody b

-- fn name, pred types, dist
cprettyDistFun :: String -> [CType] -> Dist -> Doc
cprettyDistFun fn ts (DoubleDist d _) = mkDistFunc fn (varDecls ts DoubleType) (cpretty d)
cprettyDistFun fn ts (IntDist d _) = mkDistFunc fn (varDecls ts IntType) (cpretty d)
-- FINISH vvv -- how are dists to be combined?
cprettyDistFun fn ts (TupleDist ds) = mkDistFunc fn (varDecls ts (TupleType ts)) (cpretty (TupleDist ds))
cprettyDistFun fn ts (FixedListDist _ d) = error "FINISH.FixedListDist"
cprettyDistFun fn ts (VarListDist d) = error "FINISH.VarListDist"

-- doc
renderCode :: Doc -> IO ()
renderCode d = displayIO stdout $ renderPretty 0.8 80 d

instance CPretty DPMix where
  cpretty dpmix = cd <$> vd where
    cd = cprettyDistFun "cluster" [] (clusterDist dpmix)
    vd = cprettyDistFun "values" [] (valuesDist dpmix)

showDPMix :: DPMix -> IO ()
showDPMix dpmix = renderCode (cpretty dpmix)
