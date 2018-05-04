
module Language.Grappa.Inference.CPrinter where

import Prelude hiding ( (<$>) )
import Text.PrettyPrint.ANSI.Leijen

import Language.Grappa.Interp.CExpr
import GHC.IO.Handle.FD


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
  cpretty (DoubleDist e bs) = (cpretty e)
  cpretty (IntDist e bs) = (cpretty e)
  --                       v ???
  cpretty (TupleDist ds) = tupled(map cpretty ds)
  cpretty (FixedListDist c d) = (int c) <+> cpretty d
  cpretty (VarListDist d) = cpretty d

mkVar :: String -> Int -> String
mkVar s i = s ++ (show i)

-- pred types, last type, name prefix
varNames :: [CType] -> CType -> String -> [String]
varNames ts f p =
  let l = length ts in
  concat [map (\n -> p ++ (show n)) [0..l-2], [p ++ show (l-1)]]

-- 
mkDecls :: [(CType,String)] -> [Doc]
mkDecls ds = map (\t -> (cpretty $ fst t) <+> text (snd t)) ds

-- pred types, last type
varDecls :: [CType] -> CType -> Doc
--varDecls ts f = tupled $ mkDecls (zip ts (varNames ts f "x"))
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

-- doc
renderCode d = displayIO stdout $ renderPretty 0.8 80 d

instance CPretty DPMix where
  cpretty dpmix = (cpretty $ clusterDist dpmix) <$> (cpretty $ valuesDist dpmix)

showDPMix :: DPMix -> String
showDPMix dpmix = show (cpretty dpmix)




-- ------------------------------------------------------------
-- REMOVE
uniformDistX :: VarName -> CExpr -> CExpr -> Dist
uniformDistX var lo hi =
  DoubleDist
  (CondExpr
   -- If (lo <= var && var <= hi)
   (BinaryExpr
    AndOp
    -- lo <= var
    (BinaryExpr LteOp lo (VarExpr var))
    -- var <= hi
    (BinaryExpr LteOp (VarExpr var) hi)
   )
   -- Then return log (1 / (hi - lo))
   (log (1 / (hi - lo)))
   -- Else return -INF
   (log 0))
  -- No gradients for the uniform dist
  []

tcp = renderCode $ cprettyDistFun "foo" [DoubleType, DoubleType] (uniformDistX (VarName 0) 0 100)
