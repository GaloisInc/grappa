{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Grappa.Frontend.Errors where

import AlexTools (SourcePos(..))
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Language.Haskell.TH as TH
import Text.PrettyPrint.ANSI.Leijen

import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.Parser
import Language.Grappa.Frontend.Resolve
import Language.Grappa.Frontend.IngestEmitType
import Language.Grappa.Frontend.TypeCheck

instance Pretty ParseError where
  pretty (ParseError Nothing str) =
    text "Parse error at an unknown location: unexpected token"
    <+> text str
  pretty (ParseError (Just loc) str) =
    text "Parse error at" <+> integer row <> char ':' <> integer col <>
    text ": unexpected token" <+> text str
      where row = fromIntegral (sourceLine loc)
            col = fromIntegral (sourceColumn loc)

instance Pretty ResolveError where
  pretty (ResErrorUnbound n) =
    text "Variable not in scope:" <+> squotes (text (T.unpack n))
  pretty (ResErrorUnboundType n) =
    text "Not in scope: type constructor or class" <+> squotes (text (T.unpack n))
  pretty (ResErrorNotDefVar n) =
    text "Global name not in scope:" <+> squotes (text (TH.nameBase n))
  pretty (ResErrorNotCtor n) =
    text "Constructor not in scope:" <+> squotes (text (TH.nameBase n))
  pretty (ResErrorIngest err) = pretty err

instance Pretty IngestError where
  pretty (IngErrorMalformedType t) =
    text "Malformed type:" <+> squotes (text (TH.pprint t))
  pretty (IngErrorMalformedADT t) =
    text "Malformed ADT:" <+> squotes (text (TH.pprint t))
  pretty (IngErrorMalformedBaseType t) =
    text "Malformed base type:" <+> squotes (text (TH.pprint t))
  pretty (IngErrorMalformedADTCtor t) =
    text "Malformed ADT constructor:" <+> squotes (text (TH.pprint t))
  pretty (IngErrorMalformedBaseCtor t) =
    text "Malformed base constructor:" <+> squotes (text (TH.pprint t))
  pretty (IngErrorMalformedConstr t) =
    text "Malformed constraint:" <+> squotes (text (TH.pprint t))
  pretty (IngErrorNonTVarAsTVar tvar _role) =
    text "Malformed type: type variable used at multiple roles:" <+>
    squotes (text (TH.pprint tvar))
  pretty (IngErrorMultipleRoles t rs) =
    text "Malformed type: type variable used at multiple roles:" <+>
    squotes (text (TH.pprint t)) <+>
    parens (text "treated as" <+> text (show rs))
  pretty (IngErrorUnknownSupport t) =
    text "Unknown support type:" <+> text (TH.pprint t)
  pretty (IngErrorNonGExpr t) =
    text "Expected interp__ variant to have GExpr type, but found" <+>
    text (TH.pprint t)
  pretty (IngErrorMalformedInterpType t) =
    text "Unexpected interp__ type:" <+> text (TH.pprint t)
  pretty (IngErrorDifferentTypes t1 t2) =
    text "Normal type and interp__ type differ:" <+>
    pretty t1 <+> text "and" <+> pretty t2
  pretty (IngErrorMalformedTopInterpType t1) =
    text "Malformed top-level interp__ type:" <+>
    squotes (text (TH.pprint t1))
  pretty (IngErrorContext i ctx) =
    pretty i <$$> pretty ctx

instance Pretty IngestErrorContext where
  pretty (IngestCtxTopType t) =
    text "In ingesting top type" <+> text (TH.pprint t)
  pretty (IngestCtxConstr t) =
    text "In ingesting constructor" <+> text (TH.pprint t)
  pretty (IngestCtxType t) =
    text "In ingesting type" <+> text (TH.pprint t)
  pretty (IngestCtxInterpType t) =
    text "In ingesting interp__ type" <+> text (TH.pprint t)
  pretty (IngestCtxName t) =
    text "In ingesting variable" <+> text t

instance Pretty EmitError where
  pretty (EmitErrUnknownTypeVar t) =
    text "Emit error: unknown type variable: " <+> pretty t

instance Pretty TypeError where
  pretty (ErrorNotEqual t1 t2) =
    text "Type" <+> squotes (pretty t1) <+> text "and" <+> squotes (pretty t2)
    <+> text "are not equal"
  pretty (ErrorOccurs var t) =
    text "Occurs" <+> squotes (pretty var) <+> text "in" <+> squotes (pretty t)
  pretty (ErrorTooGeneral tt t) =
    text "Type too general:" <+> squotes (pretty t) <+> text "in" <+> squotes (pretty tt)
  pretty (ErrorCaseArity) =
    text "Wrong number of case arguments"
  pretty (ErrorCtorWrongArity ct n) =
    text "Wrong number of arguments" <+> parens (integer (fromIntegral n)) <+>
    text "to constructor" <+>  squotes (pretty ct)
  pretty (ErrorNotArrowType t) =
    text "Expected arrow type, got" <+> squotes (pretty t)
  pretty (ErrorNotTupleType n t) =
    text "Expected" <+> integer (fromIntegral n) <> text "-tuple, got" <+>
    squotes (pretty t)
  pretty (ErrorNotDistType t) =
    text "Expected distribution type, got" <+> squotes (pretty t)
  pretty (ErrorNotBaseType t) =
    text "Expected base type, got" <+> squotes (pretty t)
  pretty (ErrorNotListType t) =
    text "Expected list type, got" <+> squotes (pretty t)
  pretty (ErrorBadDeclTypeAnnot d) =
    text "Bad type annotation on declaration" <+> squotes (pretty d)
  pretty (ErrorUnsampledVar i) =
    text "Unsampled variable:" <+> squotes (text (T.unpack i))
  pretty (ErrorVarNotInScope i) =
    text "Variable not in scope" <+> squotes (text (T.unpack i))
  pretty (ErrorUnsampledVars is) =
    text "Unsampled variables" <+>
      sep (map (squotes . text . T.unpack) (F.toList is))
  pretty (ErrorEmit err) =
    text "Error emitting type:" <+> pretty err
  pretty (ErrorIngest err) =
    text "Error ingesting type:" <+> pretty err
  pretty (ErrorMisc str) =
    text "Miscellaneous error:" <+> text str
  pretty (ErrorContext e ctx) =
    pretty e <$$> nest 2 (pretty ctx)

ppMbType :: Maybe Type -> Doc
ppMbType Nothing  = text ""
ppMbType (Just t) = text "of inferred type" <+> squotes (pretty t)

instance Pretty TypeErrorContext where
  pretty (ErrorCtxExp ee typ) =
    text "in expression" <+> squotes (pretty ee) <+> ppMbType typ
  pretty (ErrorCtxVExp ve typ) =
    text "in V-expression" <+> squotes (pretty ve) <+> ppMbType typ
  pretty (ErrorCtxSourceExp se typ) =
    text "in source expression" <+> squotes (pretty se) <+> ppMbType typ
  pretty (ErrorCtxStmt ReturnStmt _) =
    text "in end of model"
  pretty (ErrorCtxStmt stmt _) =
    text "in statement" <+> squotes (ppStmtShort stmt)
  pretty (ErrorCtxGPStmt cp _) =
    text "in gprior statement" <+> squotes (pretty cp)
  pretty (ErrorCtxPattern pat typ) =
    text "in pattern" <+> squotes (pretty pat) <+> ppMbType typ
  pretty (ErrorCtxVPattern pat typ) =
    text "in v-pattern" <+> squotes (pretty pat) <+> ppMbType typ
  pretty (ErrorCtxDecl decl _) =
    text "in declaration" <+> squotes (ppDeclShort decl)
  pretty (ErrorCtxUnify t1 t2) =
    text "in trying to unify" <+> pretty t1 <+> text "and" <+> pretty t2
  pretty (ErrorCtxGenExp ge typ) =
    text "in generator expression" <+> squotes (pretty ge) <+> ppMbType typ
