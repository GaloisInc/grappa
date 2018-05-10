
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

instance CPretty Literal where
  cpretty (DoubleLit d) = double d
  cpretty (IntLit i) = int i

instance CPretty VarName where
  cpretty (VarName n) = text $ "x" <> show n

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
valueArrayProj tup off IntType =
  (cpretty tup) <> brackets(cpretty off) <> text ".int_value"
valueArrayProj tup off (TupleType _) =
  (char '&') <> parens(cpretty tup) <> brackets(cpretty off)
valueArrayProj tup off (FixedListType _ _) =
  (char '&') <> parens(cpretty tup) <> brackets(cpretty off)
valueArrayProj tup off (VarListType _) =
  (cpretty tup) <> brackets(cpretty off) <> text ".var_array_value"

instance CPretty CExpr where
  cpretty (LitExpr l) = cpretty l
  cpretty (VarExpr v) = cpretty v
  cpretty (UnaryExpr o e) = parens((cpretty o) <> cpretty e)
  cpretty (BinaryExpr o el er) = parens(nest 2 (sep [cpretty el, (cpretty o) <+> cpretty er]))
  cpretty (FunCallExpr f as) = group((text f) <> (tupled $ map cpretty as))
  cpretty (NamedVarExpr s) = text s
  cpretty (CondExpr t c a) = parens(nest 2 (vcat [(cpretty t), (char '?') <+> (cpretty c), (char ':') <+> (cpretty a)]))
  cpretty (TupleProjExpr ts e i) = valueArrayProj e (LitExpr $ IntLit $ sum(map size $ take i ts)) (ts !! i)
  cpretty (FixedListProjExpr t elist eix) = valueArrayProj elist (eix * LitExpr (IntLit (size t))) t
  cpretty (VarListProjExpr t elist eix) = error "FINISH.VarListProjExpr"

instance CPretty Dist where
  cpretty (DoubleDist e _) = (cpretty e)
  cpretty (IntDist e _) = (cpretty e)
  -- FIX: recur to emit dist funcs ref'd by td, then emit td func
  cpretty (TupleDist ds) = cat $ punctuate (space <> (char '+') <> space) (map cpretty ds)
  cpretty (FixedListDist c d) = (int c) <+> cpretty d
  cpretty (VarListDist d) = cpretty d

mkVar :: String -> Int -> String
mkVar s i = s ++ (show i)

-- pred types, last type, name prefix
varNames :: [String]
varNames = map (\i -> "x" ++ show (i :: Int)) [0..]

-- [(type, name)]
mkDecls :: [(String,CType)] -> [Doc]
mkDecls ds = map (\t -> (cpretty $ snd t) <+> text (fst t)) ds

-- type, name, initializer
mkVarDecl :: CType -> String -> Maybe Doc -> Doc
mkVarDecl t n (Just i) = (cpretty t) <+> text n <+> char '=' <+> i <> semi
mkVarDecl t n Nothing = (cpretty t) <+> text n <> semi

-- 
mkReturn :: Doc -> Doc
mkReturn d = text "return" <+> d <> semi

-- [(name,type)]
varDecls :: [(String,CType)] -> Doc
varDecls ds = encloseSep lparen rparen (comma <> space) (mkDecls ds)

-- body
mkBody :: Doc -> Doc
mkBody b = lbrace <$> (indent 4 b) <$> rbrace <> line

-- fn name, decls, body
mkDistFunc :: String -> Doc -> Doc -> Doc
mkDistFunc f ds b = (text "double") <+> text("pdf_" ++ f) <+> ds <+> mkBody b

mkExtFunc :: String -> Int -> String
mkExtFunc n i = n ++ "_" ++ show i

-- fn name, pred types, dist
cprettyDistFun :: String -> [CType] -> Dist -> Doc
cprettyDistFun fn ts (DoubleDist d _) =
  mkDistFunc fn (varDecls $ zip varNames (ts ++ [DoubleType])) (mkReturn $ cpretty d)
cprettyDistFun fn ts (IntDist d _) =
  mkDistFunc fn (varDecls $ zip varNames (ts ++ [IntType])) (mkReturn $ cpretty d)
-- FIX: recur to emit dist funcs ref'd by td, then emit td func
cprettyDistFun fn ts da@(TupleDist ds) =
  vcat
  (map (\(d,i) -> cprettyDistFun (mkExtFunc fn i) (ts ++ map distType (take i ds)) d)
   (zip ds [0..])
   ++
   [mkDistFunc fn (varDecls (zip varNames ts ++ [("tup", distType da)])) $
    vcat
    (map (\(d,i) ->
          mkVarDecl (distType d) ("x" ++ show (length ts + i))
          (Just $
           valueArrayProj (NamedVarExpr "tup") (LitExpr $ IntLit i)
           (distType d)))
         (zip ds [0..])
     ++ [mkReturn $ cpretty $ sum $
         map (\i -> FunCallExpr ("pdf_" ++ mkExtFunc fn i)
                    (map (VarExpr . VarName) [0..(length ts + i)]))
         [0..(length ds - 1)]])])
cprettyDistFun fn ts (FixedListDist _ d) = error "FINISH.FixedListDist"
cprettyDistFun fn ts (VarListDist d) = error "FINISH.VarListDist"

-- doc
renderCode :: Doc -> IO ()
renderCode d = displayIO stdout $ renderPretty 0.8 72 d

instance CPretty DPMix where
  cpretty dpmix = cd <$> vd where
    cd = cprettyDistFun "cluster" [] (clusterDist dpmix)
    vd = cprettyDistFun "values" [distType $ clusterDist dpmix] (valuesDist dpmix)

showDPMix :: DPMix -> IO ()
showDPMix dpmix = renderCode (cpretty dpmix)
