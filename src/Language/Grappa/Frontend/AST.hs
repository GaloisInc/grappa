{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds, TypeFamilies, GADTs, EmptyCase #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Grappa.Frontend.AST where

import qualified Data.Foldable as F
import Data.List
import qualified Data.Text as T
import qualified Language.Haskell.TH as TH

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import GHC.Exts (Constraint)

import Control.Monad.State

import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals

import Text.PrettyPrint.ANSI.Leijen ((<+>), (<>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP


--
-- * Misc Helper Definitions
--

-- | The 'Enabled' type is a trivial way of "turning off" certain ADT
-- constructors in certain contexts. A value of type @'Enabled' 'True@
-- has a single constructor 'Enabled', while a value of type
-- @'Enabled' False@ cannot be constructed at all.
data Enabled b where
  Enabled :: Enabled 'True

instance Show (Enabled b) where
  show Enabled = "Enabled"

-- | If we have a variable of type @'Enabled 'False@, we call this
-- 'notEnabled' function on it to discharge our obligation to handle
-- that case.
notEnabled :: Enabled 'False -> a
notEnabled e = case e of { }

deriving instance Eq (Enabled 'True)

-- | Show an object with parentheses around it
showParens :: Show a => a -> String
showParens a = "(" ++ show a ++ ")"

-- | Captures that all computations in one monad can be embedded in another
class SubMonad msub m where
  embedM :: msub a -> m a


--
-- * Data Kind Defining Phases of Grappa Compilation
--

-- ** Overall Compiler Phases

-- | This is a data-type representing the current phase of the compile
-- process. This type is used as a type-level index for various
-- phases of the compiler
data CompilerPhase
  = RawPhase
  | ResolvedNamesPhase
  | PreTypedPhase
  | TypedPhase
    deriving (Eq, Show)

-- These aliases let us avoid the tick and also keep
-- backwards-compatibility with the older system
type Raw           = 'RawPhase
type ResolvedNames = 'ResolvedNamesPhase
type PreTyped      = 'PreTypedPhase
type Typed         = 'TypedPhase

-- | @'GName' p@ is the type we use to represent global names: it
-- starts as a raw identifier, and after the resolution phase also
-- includes other information about the name.
type family GName (p :: CompilerPhase) :: * where
  GName Raw   = Ident
  GName other = ResGName

-- | @'CtorName' p@ is the type we use to represent constructors: it
-- starts as a raw identifier, and after the resolution phase also
-- includes other information about the constructor
type family CtorName (p :: CompilerPhase) :: * where
  CtorName Raw   = Ident
  CtorName other = CtorInfo

-- | @'OpInfo' p@ is the type of metadata about operator symbols: it
-- starts as '()' and, after resolution, turns to the fixity of that
-- operator.
type family OpInfo (p :: CompilerPhase) :: * where
  OpInfo Raw   = ()
  OpInfo other = TH.Fixity

-- | @'GetHasSugar' p@ is a type-level boolean telling us whether we have
-- expressions representing syntactic sugar left in the AST.
type family GetHasSugar (p :: CompilerPhase) :: Bool where
  GetHasSugar Raw           = 'True
  GetHasSugar ResolvedNames = 'True
  GetHasSugar other         = 'False

-- | @'SugarEnabled' p@ is a type that is only inhabited if we have
-- syntactic sugar expressions left in the AST. By including a value
-- of this type in an AST node, that node becomes impossible to
-- construct after desugaring.
type SugarEnabled p = Enabled (GetHasSugar p)

-- | @'GetTypePhase' p@ is a type of kind 'TypePhase', which represents
-- the current state of known type information in the compiler.
type family GetTypePhase (p :: CompilerPhase) :: TypePhase where
  GetTypePhase Raw   = RawType
  GetTypePhase other = TypedType

-- | @'SrcVarName' p@ is the type of identifiers in source-expressions; this
-- starts as 'Ident' and eventually becomes identified Template Haskell names
type family SrcVarName (p :: CompilerPhase) :: * where
  SrcVarName Raw   = Ident
  SrcVarName other = TH.Name

-- | @'TypeAnnot' p@ is the type of type annotations in AST nodes;
-- this starts as '()' and becomes 'Type' after the type-checking
-- phase.
type family TypeAnnot (p :: CompilerPhase) :: * where
  TypeAnnot Typed     = TypeP TypedType
  TypeAnnot other     = ()

-- | @'DeclTypeAnnot' p@ is the type of type annotations on top-level
-- declarations; this starts as a 'Maybe' value over the current type
-- representation, and turns to 'Type' once we have finished
-- type-checking.
type family DeclTypeAnnot (p :: CompilerPhase) :: * where
  DeclTypeAnnot Typed     = TopTypeP TypedType
  DeclTypeAnnot other = Maybe (TopTypeP (GetTypePhase other))

type family InferenceMethodName (p :: CompilerPhase) :: * where
  InferenceMethodName Raw   = Ident
  InferenceMethodName other = InferenceMethod

-- ** Type Phases

-- | This type represents the representation of types at different
-- phases in our compile process.
data TypePhase
  = RawTypePhase
  | TypedTypePhase
    deriving (Eq, Show)

-- These let us keep backwards-compatibility with the older method
type RawType   = 'RawTypePhase
type TypedType = 'TypedTypePhase

-- | @'TypeVar' p@ represents the type of type variables; for raw
-- types, this is a raw identifier, and after type-checking, it is our
-- 'TVar' type.
type family TypeVar (p :: TypePhase) :: * where
  TypeVar RawType   = Ident
  TypeVar TypedType = TVar

-- | @'TypeName' p@ represents the type of our type names; for raw
-- types, this is a raw identifier, and after type-checking, it is our
-- 'TypeNameInfo' type.
type family TypeName (p :: TypePhase) :: * where
  TypeName RawType   = Ident
  TypeName TypedType = TypeNameInfo

-- | @'ConstrName' p@ represents the type of our constraint names; for
-- raw types, this is a raw identifier, and after type-checking, it is
-- our 'ConstrInfo' type.
type family ConstrName (p :: TypePhase) :: * where
  ConstrName RawType   = Ident
  ConstrName TypedType = ConstrInfo

-- ** Constraint aliases across phases

-- | States that all the elements of a 'TypePhase' satisfy a constraint
type TypePhaseC (c :: * -> Constraint) p =
  ( c (ConstrName p)
  , c (TypeVar p)
  , c (TypeName p)
  )

-- | States that all the elements of a 'Phase' satisfy a constraint
type PhaseC (c :: * -> Constraint) p =
  ( c (GName p)
  , c (CtorName p)
  , c (SrcVarName p)
  , c (TypeAnnot p)
  , c (DeclTypeAnnot p)
  , c (InferenceMethodName p)
  , TypePhaseC c (GetTypePhase p)
  )

--
-- * Grappa Types and Type Variables
--

-- | Variables are represented by integers
data TVar = TVar Int deriving (Eq,Ord)

instance Show TVar where
  show (TVar i) = "X" ++ show i

-- | The Grappa types. NOTE: the difference between a base type and an ADTType
-- is that base types do not allow compound distributions over them
data TypeP p
  = VarType (TypeVar p)
  | BaseType (TypeName p) [TypeP p]
  | ADTType (TypeName p) [TypeP p]
  | TupleType [TypeP p]
  | DistType (TypeP p)
  | ArrowType (TypeP p) (TypeP p)
  | UnusedType
    -- ^ The 'UnusedType' constructor is relevant in source expressions, to
    -- specifically mark a field that gets read but never used

deriving instance (Eq (TypeVar p), Eq (TypeName p)) => Eq (TypeP p)
deriving instance (Ord (TypeVar p), Ord (TypeName p)) => Ord (TypeP p)

-- We write this manually to make the printing a little nicer...
instance (Show (TypeVar p), Show (TypeName p)) => Show (TypeP p) where
  show (VarType var) = show var
  show (BaseType nm args) =
    "(Base " ++ show nm ++ intercalate ", " (map showParens args) ++ ")"
  show (ADTType nm args) =
    "(ADT " ++ show nm ++ intercalate ", " (map showParens args) ++ ")"
  show (TupleType args) =
    "(" ++ intercalate ", " (map show args) ++ ")"
  show (DistType vtp) = "(Dist " ++ show vtp ++ ")"
  show (ArrowType dom_tp ran_tp) =
    "(" ++ show dom_tp ++ " -> " ++ show ran_tp ++ ")"
  show UnusedType = "[Unused]"

-- | Type-level constraints, similar to Haskell typeclasses
data ClassConstrP p
  = NamedConstr (ConstrName p) (TypeP p)
    -- ^ An ordinary, unary, named typeclass constraint on a Grappa type
  | InterpConstr (ConstrName p) [TypeP p]
    -- ^ Constraint stating that a Haskell function or operator can be
    -- interpreted at the given type(s) in the current representation. The name
    -- used is of the form @Interp__XXX@ where @XXX@ is a conversion of the
    -- operator name to a valid Haskell identifier. The corresponding Haskell
    -- type constraint is @Interp__XXX repr a1 .. an@, where @repr@ is a type
    -- variable for the current representation and the @ai@ are the types in the
    -- type list.
  | InterpADTConstr (TypeName p) [TypeP p]
    -- ^ An 'Interp__ADT' constraint, stating that the given Grappa ADT type can
    -- be interpreted in a particular representation. The corresponding Haskell
    -- type constraint is of the form @Interp__ADT repr a1 .. an@, where @repr@
    -- is a type variable for the current representation and the @ai@ are the
    -- types in the type list.

deriving instance TypePhaseC Eq p => Eq (ClassConstrP p)
deriving instance TypePhaseC Ord p => Ord (ClassConstrP p)
deriving instance TypePhaseC Show p => Show (ClassConstrP p)

-- | Top-level types (FIXME: document this!)
data TopTypeP p = TopType [TVar] [ClassConstrP p] [TypeP p] (TypeP p)

deriving instance TypePhaseC Eq p => Eq (TopTypeP p)
deriving instance TypePhaseC Ord p => Ord (TopTypeP p)
deriving instance TypePhaseC Show p => Show (TopTypeP p)


--
-- * Grappa Declarations, Statements, and Expressions
--

type Ident = T.Text

data Filename
  = FileStringLit T.Text
  | FileVarName T.Text
    deriving (Eq, Show)

interpIdent :: Ident -> Ident
interpIdent t = T.pack "interp__" `T.append` T.concatMap go t
  where go '+' = T.pack "'plus"
        go '-' = T.pack "'minus"
        go '*' = T.pack "'times"
        go '/' = T.pack "'div"
        go '!' = T.pack "'bng"
        go '#' = T.pack "'oct"
        go '$' = T.pack "'dol"
        go '%' = T.pack "'per"
        go '&' = T.pack "'amp"
        go '.' = T.pack "'dot"
        go '<' = T.pack "'lt"
        go '=' = T.pack "'eq"
        go '>' = T.pack "'gt"
        go '?' = T.pack "'qmk"
        go '@' = T.pack "'at"
        go '\\' = T.pack "'bsl"
        go '^' = T.pack "'crt"
        go '|' = T.pack "'bar"
        go '~' = T.pack "'tld"
        go c   = T.singleton c

-- | Top-level declarations
data Decl p
  = FunDecl Ident (DeclTypeAnnot p) [FunCase p]
    -- ^ A function (or model, which is represented as a function that returns
    -- an anonymous model) has a name, a type, and a set of cases
  | SourceDecl Ident (TypeP (GetTypePhase p)) (SourceExp p)
    -- ^ A source declaration is a name, a type, and a source expression
  | MainDecl (GPriorStmt p) (AppliedInfMethod p)

-- | Parameter for an inference method; the 'ipType' can have variable 0 free,
-- to refer to the support type of the distribution being passed to the method
data InferenceParam = InferenceParam
  { ipName        :: String
  , ipDescription :: String
  , ipType        :: Type
  } deriving (Eq, Show)

-- | An inference method, including documentation and information on how to
-- compile it to Template Haskell
data InferenceMethod = InferenceMethod
  { imName         :: String
  , imDescription  :: String
  , imParams       :: [InferenceParam]
  , imRunFunc      :: TH.Name
  , imModelCopies  :: Int
  } deriving (Eq, Show)

-- | An inference method fully applied to arguments
data AppliedInfMethod p = AppliedInfMethod
  { infName   :: InferenceMethodName p
  , infParams :: [Exp p]
  }

-- | A model case determines a probabilistic computation for a portion of the
-- input space of a model. It is given as a pattern for the portion of the input
-- space it covers, an expression giving the probability of this particular
-- case, and a 'Stmt' describing the distribution for this case.
data ModelCase p = ModelCase (Pattern p) (Exp p) (Stmt p)

-- | A case branch for a function definition, which contains a list of patterns
-- for the @N@ arguments of the function followed by the body of the function
-- for that particular branch
data FunCase p = FunCase [Pattern p] (Exp p)

data Pattern p
  = VarPat Ident (TypeAnnot p)
  | WildPat (TypeAnnot p)
  | CtorPat (CtorName p) [Pattern p] (TypeAnnot p)
  | TuplePat [Pattern p] (TypeAnnot p)
  | LitPat Literal (TypeAnnot p)
  | SigPat (Pattern p) (TypeP (GetTypePhase p))

data StmtCase p = StmtCase (Pattern p) (Stmt p) (TypeAnnot p)

data Stmt p
  = ReturnStmt
  | SampleStmt (VExp p) (Exp p) (Stmt p)
  | LetStmt Ident (Exp p) (Stmt p)
  | CaseStmt (Exp p) [StmtCase p]

data ExpCase p = ExpCase (Pattern p) (Exp p) (TypeAnnot p) (TypeAnnot p)

data Exp p
  = NameExp (Name p) (TypeAnnot p)
  | LiteralExp Literal (TypeAnnot p)
  | SigExp (Exp p) (TypeP (GetTypePhase p))
  | AppExp (Exp p) [Exp p] (TypeAnnot p)
  | TupleExp [Exp p] (TypeAnnot p)
  | OpExp (SugarEnabled p) (Maybe (Exp p)) (GName p) (Exp p)
  | ParensExp (SugarEnabled p) (Exp p)
  | ListExp (SugarEnabled p) [Exp p]
  | LetExp Ident (TypeAnnot p) (Exp p) (Exp p) (TypeAnnot p)
  | CaseExp (Exp p) [ExpCase p] (TypeAnnot p)
  | IfExp (Exp p) (Exp p) (Exp p) (TypeAnnot p)
  | FunExp (FunCase p) (TypeAnnot p)
  | ModelExp [ModelCase p] (TypeAnnot p)

-- | Expressions that can occur on the left-hand side of a sample statement
data VExp p
  = VarVExp Ident Bool (TypeAnnot p)
    -- ^ The Boolean flag is true iff the variable is already in scope, and is
    -- being sampled, or false if this v-expression binds it as a fresh variable
  | WildVExp (TypeAnnot p)
  | CtorVExp (CtorName p) [VExp p] (TypeAnnot p)
  | TupleVExp [VExp p] (TypeAnnot p)
  | SigVExp (VExp p) (TypeP (GetTypePhase p))
  | EmbedVExp (Exp p) (TypeAnnot p)

data GPriorStmt p
  = GPriorStmt (SourceExp p) (Exp p)

-- | Expressions that represent data sources
data SourceExp p
  = VarSrcExp (SrcVarName p) (TypeAnnot p)
  | BoundVarSrcExp Ident (TypeAnnot p)
  | WildSrcExp (TypeAnnot p)
  | LiteralSrcExp Literal (TypeAnnot p)
  | CtorSrcExp (CtorName p) [SourceExp p] (TypeAnnot p)
  | TupleSrcExp [SourceExp p] (TypeAnnot p)
  | FileSrcExp Filename Ident (TypeAnnot p)
    -- ^ Contains the filename, the format, and the type
  | ListCompSrcExp (SourceExp p) [ListCompArm p] (TypeAnnot p)

-- | A 'ListCompArm' is a binding of the form @Pattern <- GenExp@
data ListCompArm p = ListCompArm (Pattern p) (GenExp p)

-- | A 'GenExp' is something which can be used in generating a list
-- comprehension.
data GenExp p
  = VarGenExp (SrcVarName p) (TypeAnnot p)
  | BoundVarGenExp Ident (TypeAnnot p)
  | FileGenExp Filename Ident (TypeAnnot p)
  | RangeGenExp Integer (Maybe Integer) Integer (TypeAnnot p)

data Name p = LocalName Ident
            | GlobalName (GName p)
            | CtorName (CtorName p)

-- | Literals
data Literal = IntegerLit Integer
             | RationalLit Rational
             deriving (Show, Eq, Ord)


deriving instance (Show (GName p), Show (CtorName p)) => Show (Name p)
deriving instance PhaseC Show p => Show (VExp p)
deriving instance PhaseC Show p => Show (SourceExp p)
deriving instance PhaseC Show p => Show (GenExp p)
deriving instance PhaseC Show p => Show (ListCompArm p)
deriving instance PhaseC Show p => Show (Exp p)
deriving instance PhaseC Show p => Show (ExpCase p)
deriving instance PhaseC Show p => Show (StmtCase p)
deriving instance PhaseC Show p => Show (Stmt p)
deriving instance PhaseC Show p => Show (GPriorStmt p)
deriving instance PhaseC Show p => Show (Pattern p)
deriving instance PhaseC Show p => Show (FunCase p)
deriving instance PhaseC Show p => Show (ModelCase p)
deriving instance PhaseC Show p => Show (Decl p)
deriving instance PhaseC Show p => Show (AppliedInfMethod p)

-- These are needed for testing purposes
deriving instance Eq (Name Raw)
deriving instance Eq (VExp Raw)
deriving instance Eq (SourceExp Raw)
deriving instance Eq (GenExp Raw)
deriving instance Eq (ListCompArm Raw)
deriving instance Eq (Exp Raw)
deriving instance Eq (ExpCase Raw)
deriving instance Eq (StmtCase Raw)
deriving instance Eq (Stmt Raw)
deriving instance Eq (GPriorStmt Raw)
deriving instance Eq (Pattern Raw)
deriving instance Eq (FunCase Raw)
deriving instance Eq (ModelCase Raw)
deriving instance Eq (Decl Raw)
deriving instance Eq (AppliedInfMethod Raw)


--
-- * Printing and Pretty-Printing
--

commaSep :: (F.Foldable f, PP.Pretty p) => f p -> PP.Doc
commaSep = PP.sep . PP.punctuate (PP.char ',') . map PP.pretty . F.toList

ppIdent :: T.Text -> PP.Doc
ppIdent = PP.text . T.unpack

ppTHName :: TH.Name -> PP.Doc
ppTHName = PP.text . TH.nameBase

instance PP.Pretty TH.Name where
  pretty = ppTHName

instance PhaseC PP.Pretty p => PP.Pretty (Decl p) where
  pretty (FunDecl n _ cs) =
    PP.vcat (PP.text "fun" <+> PP.text (T.unpack n) : concat
             [ [ PP.nest 2 $ PP.hsep (map PP.pretty ps) <+> PP.char '='
               , PP.nest 4 $ PP.pretty expr
               ]
             | FunCase ps expr <- cs
             ])
  pretty (SourceDecl n _ se) =
    PP.text "source" <+> PP.text (T.unpack n) <+> PP.pretty se
  pretty (MainDecl _ _) =
    PP.text "main" <+> PP.text "..." -- XXX FIXME

instance PhaseC PP.Pretty p => PP.Pretty (FunCase p) where
  pretty (FunCase pats expr) =
    PP.sep (map PP.pretty pats) <+> PP.char '=' <+> PP.pretty expr

ppDeclShort :: Decl p -> PP.Doc
ppDeclShort (FunDecl n _ _) = PP.text "fun" <+> PP.text (T.unpack n)
ppDeclShort (SourceDecl n _ _) = PP.text "source" <+> PP.text (T.unpack n)
ppDeclShort (MainDecl _ _) = PP.text "main" <+> PP.text "..."

instance PhaseC PP.Pretty p => PP.Pretty (Pattern p) where
  pretty (VarPat n _) = PP.text (T.unpack n)
  pretty (WildPat _) = PP.char '_'
  pretty (CtorPat n ps _) =
    PP.pretty n <+> PP.sep (map PP.pretty ps)
  pretty (TuplePat ps _) =
    PP.char '(' <> PP.sep (PP.punctuate (PP.char ',') (map PP.pretty ps))
    <> PP.char ')'
  pretty (LitPat l _) = PP.pretty l
  pretty (SigPat patt tp) =
    PP.sep [PP.pretty patt, PP.text "::", PP.pretty tp]

instance PhaseC PP.Pretty p => PP.Pretty (ModelCase p) where
  pretty (ModelCase pat gd bd) =
    withBody (PP.braces (PP.pretty pat <+> PP.char '|' <+> PP.pretty gd)
              <+> PP.char '=')
    where withBody hd = case bd of
            ReturnStmt -> hd <+> PP.text "nothing"
            ss         -> hd PP.<$$> PP.nest 2 (PP.pretty ss)

instance PhaseC PP.Pretty p => PP.Pretty (Stmt p) where
  pretty ReturnStmt = PP.text ""
  pretty (SampleStmt ve ee stmt) =
    PP.pretty ve <+> PP.char '~' <+> PP.pretty ee PP.<$$>
    PP.pretty stmt
  pretty (LetStmt ve ee stmt) =
    ppIdent ve <+> PP.char '=' <+> PP.pretty ee PP.<$$>
    PP.pretty stmt
  pretty (CaseStmt _ _) =
    error "FIXME: pretty not yet written for CaseStmt!"

ppStmtShort :: PhaseC PP.Pretty p => Stmt p -> PP.Doc
ppStmtShort ReturnStmt = PP.text ""
ppStmtShort (SampleStmt ve ee _) =
  PP.pretty ve <+> PP.char '~' <+> PP.pretty ee
ppStmtShort (LetStmt n ee _) =
  ppIdent n <+> PP.char '=' <+> PP.pretty ee
ppStmtShort (CaseStmt e _) =
  PP.text "case" <+> PP.pretty e <+> PP.text "of" PP.<$$> PP.text "..."

instance PhaseC PP.Pretty p => PP.Pretty (ExpCase p) where
  pretty (ExpCase pat expr _ _) =
    PP.pretty pat <+> PP.text "->" <+> PP.pretty expr

instance PhaseC PP.Pretty p => PP.Pretty (VExp p) where
  pretty (VarVExp n _ _) = PP.text (T.unpack n)
  pretty (WildVExp _) = PP.char '_'
  pretty (CtorVExp n vs _) =
    PP.parens (PP.pretty n <+> PP.sep (map PP.pretty vs))
  pretty (TupleVExp vs _) =
    PP.parens (PP.pretty vs)
  pretty (SigVExp vexp tp) =
    PP.sep [PP.pretty vexp, PP.text "::", PP.pretty tp]
  pretty (EmbedVExp e _) = PP.pretty e

instance PhaseC PP.Pretty p => PP.Pretty (Exp p) where
  pretty (NameExp n _) = PP.pretty n
  pretty (LiteralExp l _) = PP.pretty l
  pretty (SigExp e tp) =
    PP.sep [PP.pretty e, PP.text "::", PP.pretty tp]
  pretty (AppExp e es _) =
    PP.parens (PP.pretty e <+> PP.sep (map PP.pretty es))
  pretty (TupleExp es _) =
    PP.parens (commaSep es)
  pretty (OpExp _ (Just op) e1 e2) =
    PP.pretty e1 <+> PP.pretty op <+> PP.pretty e2
  pretty (OpExp _ Nothing op ee) =
    PP.pretty op <+> PP.pretty ee
  pretty (ParensExp _ e) =
    PP.parens (PP.pretty e)
  pretty (ListExp _ es) =
    PP.brackets (commaSep es)
  pretty (LetExp _ _ lhs rhs _) =
    PP.sep [PP.text "let" <+> PP.nest 2 (PP.pretty lhs) <+> PP.text "in",
            PP.pretty rhs]
  pretty (CaseExp e cs _) =
    PP.text "case" <+> PP.pretty e <+> PP.text "of" PP.<$$>
      PP.nest 2 (PP.hsep (map PP.pretty cs))
  pretty (ModelExp cs _) =
    PP.text "model" <+> PP.nest 2 (PP.sep (map PP.pretty cs))
  pretty (IfExp e c t _) =
    PP.text "if" <+> PP.pretty e <+>
    PP.text "then" <+> PP.pretty c <+>
    PP.text "else" <+> PP.pretty t
  pretty (FunExp (FunCase ps e) _) =
    PP.text "\\" <+> PP.hsep (map PP.pretty ps) <+> PP.text "->" <+> PP.pretty e

instance (PP.Pretty (CtorName p), PP.Pretty (GName p)) => PP.Pretty (Name p) where
  pretty (LocalName n) = ppIdent n
  pretty (GlobalName n) = PP.pretty n
  pretty (CtorName n) = PP.pretty n

instance PP.Pretty Literal where
  pretty (IntegerLit i) = PP.integer i
  pretty (RationalLit r) = PP.rational r

instance PP.Pretty CtorInfo where
  pretty (CtorInfo { ctor_th_name = n }) =
    PP.text (TH.pprint n)

instance PP.Pretty ResGName where
  pretty n = PP.pretty (T.unpack $ gname_ident n)

instance PP.Pretty TVar where
  pretty (TVar i) = PP.char 'x' <> PP.integer (fromIntegral i)

instance TypePhaseC PP.Pretty p  => PP.Pretty (ClassConstrP p) where
  pretty (NamedConstr n t) = PP.pretty n <+> PP.pretty t
  pretty (InterpConstr n t) =
    PP.pretty n <+> PP.text "repr" <+> PP.sep (map PP.pretty t)
  pretty (InterpADTConstr n t) =
    PP.text "Interp__ADT" <+> PP.text "repr" <+>
    PP.parens (PP.sep (PP.pretty n : map PP.pretty t))

instance TypePhaseC PP.Pretty p => PP.Pretty (TypeP p) where
  pretty (VarType v) = PP.pretty v
  pretty (BaseType n ts) =
    PP.pretty n <+> PP.sep (map PP.pretty ts)
  pretty (ADTType n ts) =
    PP.pretty n <+> PP.sep (map PP.pretty ts)
  pretty (TupleType ts) =
    PP.parens (commaSep ts)
  pretty (DistType t) =
    PP.text "dist" <+> PP.pretty t
  pretty (ArrowType t1 t2) =
    PP.pretty t1 <+> PP.text "->" <+> PP.pretty t2
  pretty UnusedType = PP.text "?unused"

instance (TypePhaseC PP.Pretty p, TypePhaseC Ord p) => PP.Pretty (TopTypeP p) where
  pretty (TopType vs cs ps p) =
    PP.sep [ PP.sep [ PP.text "forall", PP.hsep (map PP.pretty vs), PP.text "."]
           , PP.parens (commaSep $ nub $ sort cs) <+> PP.text "=>"
           , foldr arrow (PP.pretty p) ps
           ]
    where
      arrow x xs = PP.pretty x <+> PP.text "->" <+> xs

instance PhaseC PP.Pretty p => PP.Pretty (GPriorStmt p) where
  pretty (GPriorStmt se ee) =
    PP.pretty se <+> PP.char '~' <+> PP.pretty ee

instance PhaseC PP.Pretty p => PP.Pretty (SourceExp p) where
  pretty (VarSrcExp s _) =
    PP.pretty s
  pretty (BoundVarSrcExp n _) =
    PP.text (T.unpack n)
  pretty (WildSrcExp _) = PP.char '_'
  pretty (LiteralSrcExp lit _) = PP.pretty lit
  pretty (CtorSrcExp ct es _) =
    PP.pretty ct <+> PP.sep (map PP.pretty es)
  pretty (TupleSrcExp es _) =
    PP.parens (commaSep es)
  pretty (FileSrcExp file fmt _) =
    PP.text "read" <+> PP.text (show file) <+> PP.text "as" <+> ppIdent fmt
  pretty (ListCompSrcExp se arms _) =
    PP.brackets (pHead <+> PP.char '|' <+> pArms)
    where pHead = PP.pretty se
          pArms = PP.sep (PP.punctuate (PP.char '|') (fmap PP.pretty arms))

instance PhaseC PP.Pretty p => PP.Pretty (ListCompArm p) where
  pretty (ListCompArm pat ge) =
    PP.pretty pat <+> PP.text "<-" <+> PP.pretty ge

instance PhaseC PP.Pretty p => PP.Pretty (GenExp p) where
  pretty (VarGenExp name _) = PP.pretty name
  pretty (BoundVarGenExp name _) = PP.text (T.unpack name)
  pretty (FileGenExp file fmt _) =
    PP.text "read" <+> PP.text (show file) <+> PP.text "as" <+> ppIdent fmt
  pretty (RangeGenExp from to by _) =
    PP.brackets (PP.integer from <> PP.char ',' <> PP.integer (from+by) <> rest)
    where rest = case to of
            Just n -> PP.text ".." <> PP.integer n
            Nothing -> PP.empty

instance PP.Pretty InferenceMethod where
  pretty (InferenceMethod { imName = n }) = PP.text n

instance PP.Pretty TypeNameInfo where
  pretty (TypeNameInfo { tn_th_name = n }) =
    PP.text (TH.nameBase n)

instance PP.Pretty ConstrInfo where
  pretty (ConstrInfo { constr_th_name = n }) =
    PP.text (TH.nameBase n)

--
-- * Resolved Types
--

-- | Information about constructors of Grappa ADTs
data ADTCtor =
  ADTCtor { adt_ctor_th_name :: TH.Name,
            -- ^ The Template Haskell name of the constructor
            adt_ctor_args :: (TVar, [TVar], [Type])
            -- ^ The recursive type variable (used to represent recursive
            -- occurrences of the ADT), the remaining type variables of the ADT
            -- type, and the types of the arguments to the constructor (which
            -- can use the type variables)
          }
  deriving (Eq, Ord, Show)

-- | Information about constructors for "base types", i.e., Haskell types that
-- are somewhat external to Grappa
data BaseCtor =
  BaseCtor { base_ctor_th_name :: TH.Name,
             -- ^ The TH name of the constructor
             base_ctor_args :: ([TVar], [ClassConstr], [Type])
             -- ^ The free type variables, class constraints, and arguments of
             -- the constructor (which can use the free type variables)
           }
  deriving (Eq, Ord, Show)

-- | The type of resolved type names, which are either Grappa ADTs or "base
-- types", i.e., things considered somewhat external to Grappa. Note that we do
-- not store the constructors for base types in these type name structures,
-- because these could be recursive (and have infinite types), whereas our
-- Grappa ADTs always do recursion via a type variable, so are never infinite.
data TypeNameInfo = TypeNameInfo { tn_th_name :: TH.Name,
                                   tn_arity :: Int,
                                   tn_ctors :: Maybe [ADTCtor] }
                  deriving (Ord, Show)

instance Eq TypeNameInfo where
  n1 == n2 =
    tn_th_name n1 == tn_th_name n2 && tn_arity n1 == tn_arity n2

-- | The type of resolved named constraints
data ConstrInfo = ConstrInfo { constr_th_name :: TH.Name }
                deriving (Ord, Eq, Show)

-- | The phase information for types that have been resolved
-- type TypedType = 'TypePhase TVar TypeNameInfo ConstrInfo

-- | Shorthand for resolved types
type Type = TypeP TypedType

-- | Shorthand for resolved type-level constraints
type ClassConstr = ClassConstrP TypedType

-- | Shorthand for resolved top types
type TopType = TopTypeP TypedType


--
-- * Operations on Types
--

-- | The unit type as a 'TypeP'
unitType :: TypeP p
unitType = TupleType []

-- | Sets of type variables
type TVSet = Set TVar

-- | The "first" type variable
firstTVar :: TVar
firstTVar = TVar 1

-- | Generate the "next" type variable
nextTVar :: TVar -> TVar
nextTVar (TVar i) = TVar $ i + 1

-- | The set of all type variables "below" a given type variable
allTVarsBelow :: TVar -> TVSet
allTVarsBelow (TVar i) = Set.fromList $ map TVar [1..(i-1)]

-- | Build a nested arrow type from a list of domain types and a result type
mkArrowType :: [TypeP p] -> TypeP p -> TypeP p
mkArrowType [] tp = tp
mkArrowType (dom_tp:dom_tps) tp = ArrowType dom_tp $ mkArrowType dom_tps tp

-- | Do the inverse of 'mkArrowType', unfolding the type t1 -> ... -> tn -> t
-- into the pair ([t1, ..., tn], t).
--
-- NOTE: This only does __/syntactic/__ matching, and does not expand any type
-- variables, which is almost never what you want. See 'exposeArrowType'.
matchArrowType :: TypeP p -> ([TypeP p], TypeP p)
matchArrowType (ArrowType dom_tp tp) =
  let (dom_tps, _) = matchArrowType tp in
  (dom_tp:dom_tps, tp)
matchArrowType tp = ([], tp)


listTypeCons :: ADTCtor
listTypeCons = ADTCtor
  { adt_ctor_th_name = 'Cons
  , adt_ctor_args = (TVar 1, [TVar 2],
                      [VarType (TVar 2), VarType (TVar 1)])
  }

listTypeNil :: ADTCtor
listTypeNil = ADTCtor
  { adt_ctor_th_name = 'Nil
  , adt_ctor_args = (TVar 1, [TVar 2], [])
  }

-- | Build the 'TypeNameInfo' for the Grappa list type
listTypeNameInfo :: TypeNameInfo
listTypeNameInfo =
  TypeNameInfo
  { tn_th_name = ''ListF,
    tn_arity = 1,
    tn_ctors =
      Just [ listTypeNil, listTypeCons ]
  }

-- | Build a Grappa list type
mkListType :: TypeName p ~ TypeNameInfo => TypeP p -> TypeP p
mkListType elem_tp = ADTType listTypeNameInfo [elem_tp]

-- | Do the inverse of 'mkListType', matching a Grappa list type and returning
-- its element type, or returning 'Nothing' if the match fails.
--
-- NOTE: This only does __/syntactic/__ matching, and does not expand any type
-- variables, which is almost never what you want. See 'exposeListType'.
matchListType :: TypeName p ~ TypeNameInfo => TypeP p -> Maybe (TypeP p)
matchListType (ADTType tn [tp]) | tn_th_name tn == ''ListF = Just tp
matchListType _ = Nothing

-- | Build the 'TypeNameInfo' for the 'Prob' type of probabilities in Grappa
probTypeNameInfo :: TypeNameInfo
probTypeNameInfo =
  TypeNameInfo { tn_th_name = ''Prob,
                 tn_arity = 0,
                 tn_ctors = Nothing }

-- | The Grappa type of probabilities
probType :: TypeName p ~ TypeNameInfo => TypeP p
probType = BaseType probTypeNameInfo []

-- | Build the 'TypeNameInfo' for the Haskell list type
haskellListTypeNameInfo :: TypeNameInfo
haskellListTypeNameInfo =
  TypeNameInfo { tn_th_name = ''[],
                 tn_arity = 1,
                 tn_ctors = Nothing }

-- | Build a Haskell list type
mkHaskellListType :: TypeName p ~ TypeNameInfo => TypeP p -> TypeP p
mkHaskellListType elem_tp = BaseType haskellListTypeNameInfo [elem_tp]


-- | Build the 'TypeNameInfo' for a Haskell tuple type
haskellTupleTypeNameInfo :: Int -> TypeNameInfo
haskellTupleTypeNameInfo n =
  TypeNameInfo { tn_th_name = TH.tupleTypeName n,
                 tn_arity = n,
                 tn_ctors = Nothing }

-- | Build a Haskell list type
mkHaskellTupleType :: TypeName p ~ TypeNameInfo => [TypeP p] -> TypeP p
mkHaskellTupleType tps =
  BaseType (haskellTupleTypeNameInfo $ length tps) tps

boolType :: TypeName p ~ TypeNameInfo => TypeP p
boolType = BaseType info []
  where info = TypeNameInfo
          { tn_th_name = ''Bool
          , tn_arity   = 0
          , tn_ctors   = Nothing
          }

intType :: TypeName p ~ TypeNameInfo => TypeP p
intType = BaseType info []
  where info = TypeNameInfo
          { tn_th_name = ''Int
          , tn_arity = 0
          , tn_ctors = Nothing
          }

doubleType :: TypeName p ~ TypeNameInfo => TypeP p
doubleType = BaseType info []
  where info = TypeNameInfo
          { tn_th_name = ''Double
          , tn_arity = 0
          , tn_ctors = Nothing
          }

-- | Type class for monads that can generate fresh type variables
class Monad m => MonadFreshTVar m where
  freshTVar :: m TVar

-- | Generate a type from a fresh type variable
freshType :: MonadFreshTVar m => m Type
freshType = VarType <$> freshTVar

-- | Get the arity of a top-level type
topTypeArity :: TopTypeP p -> Int
topTypeArity (TopType _ _ arg_tps _) = length arg_tps


--
-- * Getting Free Type Variables
--

-- | Typeclass for getting the free type variables of an object. The single
-- method returns both two sets, of variables with positive and negative
-- occurrences in the object. The Boolean flag says whether the given object is
-- itself to be considered positive (or negative if false).
class FreeVars a where
  freeVars' :: Bool -> a -> State (TVSet,TVSet) ()

instance FreeVars TVar where
  freeVars' True var =
    modify $ \(pos,neg) -> (Set.insert var pos,neg)
  freeVars' False var =
    modify $ \(pos,neg) -> (pos, Set.insert var neg)

instance FreeVars Type where
  freeVars' dir (VarType var) = freeVars' dir var
  freeVars' dir (BaseType _ args) = mapM_ (freeVars' dir) args
  freeVars' dir (ADTType _ args) = freeVars' dir args
  freeVars' dir (TupleType args) = freeVars' dir args
  freeVars' dir (DistType vtp) = freeVars' dir vtp
  freeVars' dir (ArrowType tp1 tp2) = freeVars' dir tp1 >> freeVars' dir tp2
  freeVars' _   UnusedType = return ()

instance FreeVars ClassConstr where
  freeVars' dir (NamedConstr _ tp) = freeVars' dir tp
  freeVars' dir (InterpConstr _ tps) = freeVars' dir tps
  freeVars' dir (InterpADTConstr _ tps) = freeVars' dir tps

instance (FreeVars a, FreeVars b) => FreeVars (a,b) where
  freeVars' dir (a,b) = freeVars' dir a >> freeVars' dir b

instance (FreeVars a, FreeVars b, FreeVars c) => FreeVars (a,b,c) where
  freeVars' dir (a,b,c) = freeVars' dir a >> freeVars' dir b >> freeVars' dir c

instance FreeVars a => FreeVars [a] where
  freeVars' dir l = mapM_ (freeVars' dir) l

-- | Get all the free type variables of an object
freeVars :: FreeVars a => a -> TVSet
freeVars a =
  let (pos,neg) = snd $ runState (freeVars' True a) (Set.empty,Set.empty) in
  Set.union pos neg

-- | Get positive and negative the free (v)type variables of an object
freeVarsPosNeg :: FreeVars a => Bool -> a -> (TVSet,TVSet)
freeVarsPosNeg _ a = snd $ runState (freeVars' True a) (Set.empty,Set.empty)


containsTypeVar :: TVar -> Type -> Bool
containsTypeVar v (VarType t) = t == v
containsTypeVar v (BaseType _ args) =
  any (containsTypeVar v) args
containsTypeVar v (ADTType _ args) =
  any (containsTypeVar v) args
containsTypeVar v (TupleType args) =
  any (containsTypeVar v) args
containsTypeVar _ (DistType _) = False
containsTypeVar v (ArrowType t1 t2) =
  containsTypeVar v t1 || containsTypeVar v t2
containsTypeVar _ UnusedType = False


--
-- * Type Substitution
--

-- | Type substitutions
newtype TVSubst = TVSubst { getTVSubstMap :: Map TVar Type }

-- | Build a type substitution for a single variable
singleTVSubst :: TVar -> Type -> TVSubst
singleTVSubst var tp = TVSubst (Map.singleton var tp)

-- | Type class for things that can be substituted into
class TypeSubstitutable a where
  tpSubst :: TVSubst -> a -> a

instance TypeSubstitutable Type where
  tpSubst subst tp@(VarType var) =
    case Map.lookup var (getTVSubstMap subst) of
      Just tp' -> tp'
      Nothing -> tp
  tpSubst subst (BaseType n args) = BaseType n $ map (tpSubst subst) args
  tpSubst subst (ADTType n args) = ADTType n $ map (tpSubst subst) args
  tpSubst subst (TupleType ts) = TupleType $ map (tpSubst subst) ts
  tpSubst subst (DistType vtp) = DistType $ tpSubst subst vtp
  tpSubst subst (ArrowType t1 t2) =
    ArrowType (tpSubst subst t1) (tpSubst subst t2)
  tpSubst _ UnusedType = UnusedType


--
-- * Renaming Type Variables
--

-- | Type variable renamings
newtype TVRenaming = TVRenaming { getTVRenamingMap :: Map TVar TVar }

-- | The empty renaming
emptyTVRenaming :: TVRenaming
emptyTVRenaming = TVRenaming Map.empty

-- | Build a singleton renaming
singletonTVRenaming :: TVar -> TVar -> TVRenaming
singletonTVRenaming x y = TVRenaming (Map.singleton x y)

-- | Combine two 'TVRenaming's, returning 'Nothing' if they disagree
combineTVRenamings :: TVRenaming -> TVRenaming -> Maybe TVRenaming
combineTVRenamings (TVRenaming m1) (TVRenaming m2) =
  -- Build an intersection map that determines, for each type variable in the
  -- lhs, whether ren1 and ren2 agree on its value
  let m_inter = Map.intersectionWith (\x y -> x == y) m1 m2 in
  if and (Map.elems m_inter) then
    Just $ TVRenaming $ Map.union m1 m2
  else Nothing

-- | Type class for things (like types) that can be renamed with a 'TVRenaming'
class Renameable a where
  rename :: TVRenaming -> a -> a

instance Renameable TVar where
  rename ren var =
    case Map.lookup var (getTVRenamingMap ren) of
      Just var' -> var'
      Nothing -> error ("rename: type variable " ++ show var ++ " not found")

instance Renameable Type where
  rename ren (VarType var) = VarType $ rename ren var
  rename ren (BaseType n args) = BaseType n $ map (rename ren) args
  rename ren (ADTType n args) = ADTType n $ map (rename ren) args
  rename ren (TupleType ts) = TupleType $ map (rename ren) ts
  rename ren (DistType vtp) = DistType $ rename ren vtp
  rename ren (ArrowType t1 t2) = ArrowType (rename ren t1) (rename ren t2)
  rename _   UnusedType = UnusedType

instance Renameable ClassConstr where
  rename ren (NamedConstr cn tp) = NamedConstr cn $ rename ren tp
  rename ren (InterpConstr cn tps) = InterpConstr cn $ map (rename ren) tps
  rename ren (InterpADTConstr n tps) = InterpADTConstr n $ map (rename ren) tps

instance (Renameable a, Renameable b) => Renameable (a,b) where
  rename ren (a,b) = (rename ren a, rename ren b)

instance Renameable a => Renameable [a] where
  rename ren l = map (rename ren) l


--
-- * Syntactic Matching for Types
--

-- | Pattern-match a type up to renaming of variables
synMatch :: Type -> Type -> Maybe TVRenaming
synMatch (VarType x) (VarType y) = return $ singletonTVRenaming x y
synMatch (VarType _) _ = Nothing
synMatch (BaseType nm1 args1) (BaseType nm2 args2)
  | nm1 == nm2 = synMatchList args1 args2
synMatch (BaseType _ _) _ = Nothing
synMatch (ADTType nm1 args1) (ADTType nm2 args2)
  | nm1 == nm2 = synMatchList args1 args2
synMatch (ADTType _ _) _ = Nothing
synMatch (TupleType args1) (TupleType args2) = synMatchList args1 args2
synMatch (TupleType _) _ = Nothing
synMatch (DistType tp1) (DistType tp2) = synMatch tp1 tp2
synMatch (DistType _) _ = Nothing
synMatch (ArrowType dom_tp1 ran_tp1) (ArrowType dom_tp2 ran_tp2) =
  synMatchList [dom_tp1, ran_tp1] [dom_tp2, ran_tp2]
synMatch (ArrowType _ _) _ = Nothing
synMatch UnusedType UnusedType = return emptyTVRenaming
synMatch UnusedType _ = Nothing

-- | Pattern-match a list of types
synMatchList :: [Type] -> [Type] -> Maybe TVRenaming
synMatchList [] [] = return emptyTVRenaming
synMatchList (tp1:tps1) (tp2:tps2) =
  do ren1 <- synMatch tp1 tp2
     ren2 <- synMatchList tps1 tps2
     combineTVRenamings ren1 ren2
synMatchList _ _ = Nothing


--
-- * Resolved Declarations, Statements, and Expressions
--

-- | The type of resolved global (term) names
data ResGName = ResGName {
  gname_ident :: Ident,
  -- ^ The Grappa identifier this name came from, for printing
  gname_th_name :: TH.Name,
  -- ^ The Template Haskell identifier for this name, which is of the form
  -- @interp__XXX@ for identifier @XXX@
  gname_raw_th_name :: Maybe TH.Name,
  -- ^ The "raw" Template Haskell identifier for this name, if it exists, which
  -- is the Haskell identifier of the same name
  gname_type :: TopType,
  -- ^ The top-level type of this name
  gname_fixity :: TH.Fixity
  -- ^ The fixity for this name (only used if it is an operator)
  }

instance Show ResGName where
  show = show . gname_ident

-- | The type of resolved constructors
data CtorInfo = CtorInfo { ctor_th_name :: TH.Name,
                           ctor_type :: TopType,
                           ctor_is_adt :: Bool }
  deriving (Eq, Ord)

instance Show CtorInfo where
  show = show . ctor_th_name

-- | Get the arity of a resolved constructor
ctorArity :: CtorInfo -> Int
ctorArity ctor = topTypeArity (ctor_type ctor)

-- | Test whether a 'TypeNameInfo' refers to an ADT or base type
typeNameIsADT :: TypeNameInfo -> Bool
typeNameIsADT tn =
  case tn_ctors tn of
    Just _ -> True
    Nothing -> False

-- | Build a 'CtorInfo' from a type name and an 'ADTCtor' in that type
buildADTCtorInfo :: TypeNameInfo -> ADTCtor -> CtorInfo
buildADTCtorInfo adt adt_ctor =
  let (r, vars, dom_tps) = adt_ctor_args adt_ctor
      ran_tp = ADTType adt (map VarType vars)
      r_subst = singleTVSubst r ran_tp
      top_tp = TopType vars [] (map (tpSubst r_subst) dom_tps) ran_tp
  in
  CtorInfo { ctor_th_name = adt_ctor_th_name adt_ctor,
             ctor_type = top_tp,
             ctor_is_adt = True }

-- | Build a 'CtorInfo' from a type name and a 'BaseCtor' in that type
buildBaseCtorInfo :: TypeNameInfo -> BaseCtor -> CtorInfo
buildBaseCtorInfo base_tp base_ctor =
  let (vars, constrs, dom_tps) = base_ctor_args base_ctor
      ran_tp = BaseType base_tp (map VarType vars)
      top_tp = TopType vars constrs dom_tps ran_tp in -- XXX
  CtorInfo { ctor_th_name = base_ctor_th_name base_ctor,
             ctor_type = top_tp,
             ctor_is_adt = False }


--
-- * Operations on Declarations, Statements, and Expressions
--

-- | Get the identifier name of a top-level declaration
declName :: Decl p -> Ident
declName (FunDecl nm _ _) = nm
declName (SourceDecl nm _ _) = nm
declName (MainDecl _ _) = T.pack "main"

-- | Get the type of a top-level declaration
declType :: Decl p -> DeclTypeAnnot p
declType (FunDecl _ annot _) = annot
declType (SourceDecl _ _ _) = error "[unreachable]"
declType (MainDecl _ _) = error "[unreachable]"


funCaseArity :: FunCase p -> Int
funCaseArity (FunCase args _) = length args

-- | Get the type annotation of a pattern
patternType :: Pattern p -> TypeAnnot p
patternType (VarPat _ tp) = tp
patternType (WildPat tp) = tp
patternType (CtorPat _ _ tp) = tp
patternType (TuplePat _ tp) = tp
patternType (LitPat _ tp) = tp
patternType (SigPat patt _) =
  -- NOTE: the type on a SigPat is always TypeP p, which might not be the same
  -- as TypeAnnot p depending on what phase we are in...
  patternType patt

-- | Get the variables bound in a pattern
patternVars :: Pattern p -> Set Ident
patternVars (VarPat x _) = Set.singleton x
patternVars (WildPat _) = Set.empty
patternVars (CtorPat _ patts _) =
  Set.unions $ map patternVars patts
patternVars (TuplePat patts _) =
  Set.unions $ map patternVars patts
patternVars (LitPat _ _) = Set.empty
patternVars (SigPat patt _) = patternVars patt

-- | Get the variables bound by a list-comprehension arm
armVars :: ListCompArm Raw -> Set Ident
armVars (ListCompArm pat _) = patternVars pat

-- | Get the variables bound in a v-expression viewed as a pattern
vexpVars :: VExp p -> Set Ident
vexpVars (VarVExp x _ _) = Set.singleton x
vexpVars (WildVExp _) = Set.empty
vexpVars (CtorVExp _ vexps _) =
  Set.unions $ map vexpVars vexps
vexpVars (TupleVExp vexps _) =
  Set.unions $ map vexpVars vexps
vexpVars (SigVExp vexp _) = vexpVars vexp
vexpVars (EmbedVExp _ _) = Set.empty

-- | Smart constructor for applications
applyExp :: TypeAnnot p ~ () => Exp p -> [Exp p] -> Exp p
applyExp (AppExp f args ()) args2 = AppExp f (args ++ args2) ()
applyExp f args = AppExp f args ()

-- | Call 'applyExp' with just one argument
applyExp1 :: TypeAnnot p ~ () => Exp p -> Exp p -> Exp p
applyExp1 f arg = applyExp f [arg]


-- | Class for getting the type of expressions and related constructs
class TypeOf t where
  typeOf :: t Typed -> Type

instance TypeOf Exp where
  typeOf (NameExp _ t) = t
  typeOf (LiteralExp _ t) = t
  typeOf (SigExp _ t) = t
  typeOf (AppExp _ _ t) = t
  typeOf (TupleExp _ t) = t
  typeOf (OpExp not_en _ _ _) = notEnabled not_en
  typeOf (ParensExp not_en _) = notEnabled not_en
  typeOf (ListExp not_en _) = notEnabled not_en
  typeOf (LetExp _ _ _ _ t) = t
  typeOf (CaseExp _ _ t) = t
  typeOf (IfExp _ _ _ t) = t
  typeOf (FunExp _ t) = t
  typeOf (ModelExp _ t) = t

instance TypeOf Pattern where
  typeOf (VarPat _ tp) = tp
  typeOf (WildPat tp) = tp
  typeOf (CtorPat _ _ tp) = tp
  typeOf (TuplePat _ tp) = tp
  typeOf (LitPat _ tp) = tp
  typeOf (SigPat _ tp) = tp

instance TypeOf GenExp where
  typeOf (VarGenExp _ t) = t
  typeOf (BoundVarGenExp _ t) = t
  typeOf (FileGenExp _ _ t) = t
  typeOf (RangeGenExp _ _ _ t) = t

instance TypeOf ExpCase where
  typeOf (ExpCase _ e _ _) = typeOf e

instance TypeOf ModelCase where
  typeOf (ModelCase p _ _) = typeOf p
