{-# LANGUAGE GADTs #-}

-- | Compile Grappa programs to a C AST that can be pretty-printed to
-- produce a C program. CDynExprs are translated to C expressions and
-- CDists are compiled to PDF functions.

module Language.Grappa.Inference.CTranslate where

import           Language.C.Data.Ident
import           Language.C.Data.Node
import           Language.C.Syntax.AST
import           Language.C.Pretty
import           Language.C.Syntax.Constants
import           Text.PrettyPrint.HughesPJ

import           Language.Grappa.GrappaInternals
import           Language.Grappa.Interp.CExprGADT


-- The pretty-printer instances for CExpressions, etc. are defined
-- only for node types with their type parameter specialized to
-- NodeInfo. This is just a short name for the dummy NodeInfo value.
nil :: NodeInfo
nil = undefNode

-- A proof 'TypeListElem ts t' not only says that the type t is in the
-- type list ts, but it also specifies its exact position in the
-- list. This extracts the index corresponding to that position.
typeListElemToInt :: TypeListElem ts t -> Int
typeListElemToInt TypeListElem_Base = 0
typeListElemToInt (TypeListElem_Cons pf) = 1 + typeListElemToInt pf

stringIdent :: String -> Ident
stringIdent s = Ident s 0 undefNode

mkVar :: String -> CExpr
mkVar s = CVar (stringIdent s) nil

mkReturn :: CExpr -> CStat
mkReturn e = CReturn (Just e) nil

transCType :: CType a -> CTypeSpecifier NodeInfo
transCType DoubleType = CDoubleType nil
transCType IntType    = CIntType nil
transCType BoolType   = CBoolType nil
transCType (TupleType _) =
  CSUType (CStruct CUnionTag (Just $ stringIdent "value") Nothing [] nil) nil
transCType (ListType _)  =
  CSUType (CStruct CStructTag
           (Just $ stringIdent "var_length_array") Nothing [] nil) nil

-- Given an identifier, a type, and an optional initialization
-- expression, produce a declaration i.e. "double x = 0.0" to be used
-- in a compound block statement or function parameter list.
cTypeDeclaration :: Ident -> CType a -> Maybe CExpr -> CDeclaration NodeInfo
cTypeDeclaration nm ty e =
  CDecl [CTypeSpec $ transCType ty]
  [(Just $ CDeclr (Just nm)
    (if isBaseType ty then [] else [CPtrDeclr [] nil])
    Nothing [] nil, flip CInitExpr nil <$> e, Nothing)] nil

transLiteral :: Literal -> CConst
transLiteral (DoubleLit d) = CFloatConst (cFloat $ realToFrac d) nil
transLiteral (IntLit i)    = CIntConst (cInteger $ toInteger i) nil
transLiteral (BoolLit b)   = CIntConst (cInteger $ if b then 1 else 0) nil

transVarName :: VarName -> Ident
transVarName (VarName i) = Ident ("x" ++ show i) i undefNode

transUnaryOp :: UnaryOp -> CUnaryOp
transUnaryOp NegateOp = CMinOp
transUnaryOp NotOp    = CNegOp

transBinaryOp :: BinaryOp -> CBinaryOp
transBinaryOp PlusOp  = CAddOp
transBinaryOp TimesOp = CMulOp
transBinaryOp MinusOp = CSubOp
transBinaryOp DivOp   = CDivOp
transBinaryOp ExpOp   = error "transBinaryOp: unexpected ExpOp"
transBinaryOp LtOp    = CLeOp
transBinaryOp LteOp   = CLeqOp
transBinaryOp GtOp    = CGrOp
transBinaryOp GteOp   = CGeqOp
transBinaryOp EqOp    = CEqOp
transBinaryOp NeOp    = CNeqOp
transBinaryOp AndOp   = CAndOp
transBinaryOp OrOp    = COrOp

-- Mostly straightforward mapping of expressions.
transCDynExpr :: CDynExpr a -> CExpr
transCDynExpr (LitExpr _ lit) = CConst $ transLiteral lit
transCDynExpr (VarExpr _ i) = CVar (transVarName i) nil
transCDynExpr (UnaryExpr unop e) =
  CUnary (transUnaryOp unop) (transCDynExpr e) nil
transCDynExpr (BinaryExpr _ binop e1 e2) =
  CBinary (transBinaryOp binop) (transCDynExpr e1) (transCDynExpr e2) nil
transCDynExpr (FunCallExpr fName _ _ args) =
  CCall (mkVar fName) (hListToList (transCDynExpr) args) nil
transCDynExpr (NamedVarExpr _ nm) = mkVar nm
transCDynExpr (CondExpr b e1 e2) =
  CCond (transCDynExpr b) (Just $ transCDynExpr e1) (transCDynExpr e2) nil
transCDynExpr (TupleProjExpr ts elemPf tup) =
  tupleProj (SomeCType (projectHList ts elemPf))
  (intConst $ typeListElemToInt elemPf) (transCDynExpr tup)

intConst :: Int -> CExpr
intConst i = CConst $ CIntConst (cInteger $ toInteger i) nil

cTypeFieldName :: CType a -> Ident
cTypeFieldName DoubleType    = stringIdent "double_value"
cTypeFieldName IntType       = stringIdent "int_value"
cTypeFieldName BoolType      = stringIdent "int_value"
cTypeFieldName (TupleType _) = error "cTypeFieldName: unexpected TupleType"
cTypeFieldName (ListType _)  = stringIdent "var_array_value"

-- Given a type t, tuple expression e, and index expression i,
-- produce an expression for getting the ith element of type t of e.
tupleProj :: SomeCType -> CExpr -> CExpr -> CExpr
tupleProj (SomeCType (TupleType _)) i e =
  CUnary CAdrOp (CIndex e i nil) nil
tupleProj (SomeCType t) i e =
  CMember (CIndex e i nil) (cTypeFieldName t) False nil

-- Same as above but for variable-length lists instead of tuples.
listIndex :: CType a -> CExpr -> CExpr -> CExpr
listIndex (TupleType _) i e =
  CUnary CAdrOp (CIndex (CMember e (stringIdent "elems") True nil) i nil) nil
listIndex t i e =
  CMember (CIndex (CMember e (stringIdent "elems") True nil) i nil)
  (cTypeFieldName t) False nil

-- Translate a CDist into a list of C function definitions.
transCDist :: FunName -> SomeCDist -> [CFunDef]
transCDist = mkPdf []

-- Infinite list of identifiers x0, x1, x2, etc.
varIdents :: [Ident]
varIdents = map (\i -> stringIdent $ "x" ++ show (i :: Int)) [0..]

-- The size (in increments of sizeof(value)) of a type. Most are
-- either single word values or pointers. The only interesting case is
-- the tuple, which is stored as an array in-place.
cTypeSize :: CType a -> Int
cTypeSize (TupleType ts) = foldHList (\x acc -> cTypeSize x + acc) ts 0
cTypeSize _ = 1

someCTypeSize :: SomeCType -> Int
someCTypeSize (SomeCType t) = cTypeSize t

-- Compute the actual offset into a tuple from an index value.
tupleOffset :: CTypes as -> Int -> Int
tupleOffset HListNil _         = error "tupleOffset: empty HList"
tupleOffset (HListCons _ _) 0  = 0
tupleOffset (HListCons t ts) i = cTypeSize t + tupleOffset ts (i-1)

-- Produce a PDF function for a given distribution. It may be
-- comprised of multiple constituent distributions, so we recursively
-- generate them and actually produce a list of functions for all of
-- the PDFS. The first argument is a list of types of variables that
-- are in scope for this distribution. I.e., they are extra arguments
-- to the PDF function, preceding the main one.
mkPdf :: [SomeCType] -> FunName -> SomeCDist -> [CFunDef]
mkPdf tys nm (SomeCDist (TupleDist ds)) =
  let
    distTypes = hListToList (SomeCType . cDistType) ds
    funs      = concat $ zipWith (\d i -> mkPdf (tys ++ take i distTypes)
                                   (nm ++ "_" ++ show i) d)
                (cDistsToList ds) [0..]
    paramDecls = mkParamDecls $ zip varIdents tys ++
                 [(stringIdent "tup", SomeCType $ cDistType $ TupleDist ds)]
    localDecls = mkInitDecls $ zip3 (drop (length tys) varIdents) distTypes
                 (zipWith (\i (SomeCType ty) ->
                              tupleProj (SomeCType ty)
                              (intConst $ tupleOffset (cDistsTypes ds) i)
                             (transCDynExpr $ NamedVarExpr ty "tup"))
                   [0..] distTypes)
    funCalls = map (\i -> CCall (mkVar (nm ++ "_" ++ show i))
                     (map (flip CVar nil) (take (length tys + i + 1) varIdents))
                          nil)
               [0..length distTypes - 1]
  in
    funs ++ [mkFun (stringIdent nm) paramDecls $
             CCompound []
             (map CBlockDecl localDecls ++
               [CBlockStmt $ CReturn (Just $ mkSum funCalls) nil]) nil]

mkPdf tys nm (SomeCDist (ListDist d)) =
  let
    funs       = mkPdf tys (nm ++ "_0") (SomeCDist d)
    paramDecls = mkParamDecls $ zip varIdents tys ++
                 [(stringIdent "list", SomeCType $ cDistType $ (ListDist d))]
    accumDecl  = cTypeDeclaration (stringIdent "sum") DoubleType
                 (Just $ intConst 0)
    iDecl = cTypeDeclaration (stringIdent "i") IntType Nothing
    loop  = mkForLoop (stringIdent "i")
            (intConst $ someCTypeSize $ SomeCType $ cDistType d)
            (CMember (mkVar "list") (stringIdent "length") True nil)
            (CExpr (Just $ CAssign CAddAssOp (CVar (stringIdent "sum") nil)
                    (CCall (mkVar $ nm ++ "_0")
                     (map (flip CVar nil) (take (length tys) varIdents) ++
                       [listIndex (cDistType d) (mkVar "i") (mkVar "list")]
                     ) nil) nil) nil)
  in
    funs ++ [mkFun (stringIdent nm) paramDecls $
             CCompound []
             [CBlockDecl accumDecl, CBlockDecl iDecl, CBlockStmt loop,
              CBlockStmt $ CReturn (Just $ mkVar "sum") nil] nil]

mkPdf tys nm (SomeCDist d) =
  [mkFun (stringIdent nm)
   (mkParamDecls $ zip varIdents (tys ++ [SomeCType $ cDistType d]))
    (CCompound []
     [CBlockStmt $ CReturn (Just $ transCDynExpr $ cDistPDFExpr d) nil]
     nil)]

-- counter identifier, increment, upper bound, body
mkForLoop :: Ident -> CExpr -> CExpr -> CStat -> CStat
mkForLoop i inc ub body =
  CFor (Left $ Just $ CAssign CAssignOp (CVar i nil) (intConst 0) nil)
  (Just $ CBinary CLeOp (CVar i nil) ub nil)
  (Just $ CAssign CAddAssOp (CVar i nil) inc nil)
  body nil

-- Build an expression that sums the given list of expression.
mkSum :: [CExpr] -> CExpr
mkSum [] = intConst 0
mkSum (x:[]) = x
mkSum (x:xs) = CBinary CAddOp x (mkSum xs) nil

mkDecls :: [(Ident, SomeCType, Maybe CExpr)] -> [CDeclaration NodeInfo]
mkDecls xs = map (\(nm, SomeCType ty, v) -> cTypeDeclaration nm ty v) xs

mkParamDecls :: [(Ident, SomeCType)] -> [CDeclaration NodeInfo]
mkParamDecls = mkDecls . map (\(a, b) -> (a, b, Nothing))

mkInitDecls :: [(Ident, SomeCType, CExpr)] -> [CDeclaration NodeInfo]
mkInitDecls = mkDecls . map (\(a, b, c) -> (a, b, Just c))

mkFun :: Ident -> [CDeclaration NodeInfo] -> CStat -> CFunDef
mkFun nm paramDecls body =
  CFunDef [CTypeSpec (CDoubleType nil)]
  (CDeclr (Just nm) [CFunDeclr (Right $ (paramDecls, False)) [] nil]
   Nothing [] nil) [] body nil

mkTranslUnit :: [CFunDef] -> CTranslationUnit NodeInfo
mkTranslUnit fs = CTranslUnit (map CFDefExt fs) nil


-- | Render to IO

renderCDynExpr :: CDynExpr a -> IO ()
renderCDynExpr = putStrLn . render . pretty . transCDynExpr

-- Produce and print a C translation unit from a CDist.
renderCDist :: CDist a -> IO ()
renderCDist =
  putStrLn . render . pretty . mkTranslUnit . (mkPdf [] "DPM") . SomeCDist
