{
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns, RecordWildCards, DataKinds #-}
module Language.Grappa.Frontend.Parser where

import Language.Grappa.Frontend.Lexer
import Language.Grappa.Frontend.AST
import Language.Grappa.GrappaInternals

import qualified Data.Text as T
--import           Text.Location (Lexeme(..), Position(..), Range(..), at)
import           AlexTools
import           Text.Layout.OffSides

import Debug.Trace (trace)

}

%tokentype { Lexeme Token }

%token
  IDENT       { (matchIdent -> Just $$) }
  CONIDENT    { (matchConIdent -> Just $$) }
  OP          { (matchOp -> Just $$) }
  INTEGER     { (matchInt -> Just $$) }
  RATIONAL    { (matchRat -> Just $$) }
  STR_LIT     { (matchStrLit -> Just $$) }

  'model'     { KW K_model     $$ }
  'fun'       { KW K_fun       $$ }
  'if'        { KW K_if        $$ }
  'then'      { KW K_then      $$ }
  'else'      { KW K_else      $$ }
  'let'       { KW K_let       $$ }
  'in'        { KW K_in        $$ }
  'case'      { KW K_case      $$ }
  'of'        { KW K_of        $$ }
  'source'    { KW K_source    $$ }
  'read'      { KW K_read      $$ }
  'from'      { KW K_from      $$ }
  'as'        { KW K_as        $$ }
  'nothing'   { KW K_nothing   $$ }
  'Dist'      { KW K_Dist      $$ }
  'main'      { KW K_main      $$ }
  'using'     { KW K_using     $$ }
  'param'     { KW K_param     $$ }
  '('         { KW K_lparen    $$ }
  ')'         { KW K_rparen    $$ }
  '{'         { KW K_lbrace    $$ }
  '}'         { KW K_rbrace    $$ }
  '['         { KW K_lbracket  $$ }
  ']'         { KW K_rbracket  $$ }
  ','         { KW K_comma     $$ }
  '='         { KW K_equals    $$ }
  '~'         { KW K_tilde     $$ }
  '_'         { KW K_under     $$ }
  '|'         { KW K_bar       $$ }
  '-'         { KW K_minus     $$ }
  '\\'        { KW K_backslash $$ }
  '->'        { KW K_arrow     $$ }
  '<-'        { KW K_larrow    $$ }
  '::'        { KW K_coloncolon $$ }
  '..'        { KW K_dotdot    $$ }
  ':'         { KW K_colon     $$ }

  -- These are the synthetic indentation tokens we add
  -- after lexing
  'i;'        { Lexeme _ TInSep $$ }
  'i{'        { Lexeme _ TInStart $$ }
  'i}'        { Lexeme _ TInEnd $$ }

%monad { Parse }
%error { parseError }

%name decls decls
%name gprior gprior

%%


-- Declarations ---------------------------------------------------------------------

decls :: { [Decl Raw] }
  : list1(decl) { $1 }

decl :: { Decl Raw }
  : 'model' 'i{' sep1(model_case, 'i;') 'i}' { combine_fun_cases Nothing $3 }
  | 'fun' 'i{' sep1(fun_case,'i;') 'i}' { combine_fun_cases Nothing $3 }
  | 'source' IDENT '::' typ '=' 'i{' source_exp 'i}' { SourceDecl (fst $2) $4 $7 }
  | 'main' '=' 'i{' maindecl 'i}' { $4 }

maindecl :: { Decl Raw }
  : gprior 'i;' 'using' method { MainDecl $1 $4 }

method :: { InfMethod Raw }
  : IDENT '(' sep(exp, ',') ')' { InfMethod (fst $1) $3 }

gprior :: { GPriorStmt Raw }
  : source_exp '~' exp { GPriorStmt $1 $3 }

model_case :: { (Ident, FunCase Raw) }
  : IDENT list(arg_pattern) list1(model_subcase)
    { (fst $1, FunCase $2 (ModelExp $3 ())) }

model_subcase :: { ModelCase Raw }
  : '{' sep(vpattern,',') '}' '=' 'i{' stmt_block
    { ModelCase (patt_parens $2) (LiteralExp (IntegerLit 1) ()) $6 }
  | '{' sep(vpattern,',') '|' exp '}' '=' 'i{' stmt_block
    { ModelCase (patt_parens $2) $4 $8 }

fun_case :: { (Ident, FunCase Raw) }
  : IDENT list(arg_pattern) '=' 'i{' exp 'i}' { (fst $1, FunCase $2 $5) }

stmt_block :: { Stmt Raw }
  : 'nothing' 'i}' { ReturnStmt }
  | stmt { $1 }

stmt :: { Stmt Raw }
  : vexp '~' exp stmt_tail { SampleStmt $1 $3 $4 }
  | IDENT '=' 'i{' exp 'i}' stmt_tail { LetStmt (fst $1) $4 $6 }
  | 'case' exp 'of' 'i{' sep1(stmt_case, 'i;') 'i}' { CaseStmt $2 $5 }

stmt_tail :: { Stmt Raw }
  : 'i}'      { ReturnStmt }
  | 'i;' stmt { $2 }

stmt_case :: { StmtCase Raw }
  : pattern '->' stmt { StmtCase $1 $3 () }

exp_case :: { ExpCase Raw }
  : pattern '->' exp { ExpCase $1 $3 () () }

non_ctor_arg_pattern :: { Pattern Raw }
  : IDENT { VarPat (fst $1) () }
  | '_' { WildPat () }
  | '(' sep(pattern,',') ')' { patt_parens $2 }
  | INTEGER { LitPat (IntegerLit (fst $1)) () }
  | RATIONAL { LitPat (RationalLit (fst $1)) () }

arg_pattern :: { Pattern Raw }
  : CONIDENT { CtorPat (fst $1) [] () }
  | non_ctor_arg_pattern { $1 }

pattern :: { Pattern Raw }
  : non_ctor_arg_pattern { $1 }
  | CONIDENT list(arg_pattern) { CtorPat (fst $1) $2 () }
  | pattern '::' non_arrow_typ
    -- NOTE: the right-hand side here cannot be a typ in general, because of the
    -- shift-reduce conflict of pattern :: typ -> exp in exp_case and stmt_case,
    -- and anyway, patterns shouldn't generally have arrow type anyway
    { SigPat $1 $3 }
{- FIXME: do as-patterns! -}

arg_vpattern :: { Pattern Raw }
  : IDENT { VarPat (fst $1) () }
  | '(' sep(vpattern,',') ')' { patt_parens $2 }

vpattern :: { Pattern Raw }
  : arg_vpattern { $1 }
  | CONIDENT list(arg_vpattern) { CtorPat (fst $1) $2 () }
  | vpattern '::' typ { SigPat $1 $3 }
{- FIXME: do as-patterns! -}

vexp :: { VExp Raw }
  : arg_vexp { $1 }
  | CONIDENT list(arg_vexp) { CtorVExp (fst $1) $2 () }
  | vexp '::' typ { SigVExp $1 $3 }

arg_vexp :: { VExp Raw }
  : IDENT { VarVExp (fst $1) True () }
  | INTEGER { EmbedVExp (LiteralExp (IntegerLit (fst $1)) ()) () }
  | RATIONAL { EmbedVExp (LiteralExp (RationalLit (fst $1)) ()) () }
  | '_' { WildVExp () }
  | '(' sep(vexp,',') ')' { vexp_parens $2 }

gen_exp :: { GenExp Raw }
  : 'source' 'from' filename 'as' IDENT { FileGenExp $3 (fst $5) () }
  | '[' INTEGER '..' INTEGER ']' { RangeGenExp (fst $2) (Just (fst $4)) 1 () }
  | '[' INTEGER ',' INTEGER '..' INTEGER ']'
      { RangeGenExp (fst $2) (Just (fst $6)) (fst $4 - fst $2) () }
  | '[' INTEGER '..' ']'
      { RangeGenExp (fst $2) Nothing 1 () }
  | '[' INTEGER ',' INTEGER '..' ']'
      { RangeGenExp (fst $2) Nothing (fst $4 - fst $2) () }
  | 'source' IDENT { VarGenExp (fst $2) () }
  | IDENT { VarGenExp (fst $1) () }

exp :: { Exp Raw }
  : 'let' IDENT '=' 'i{' exp 'i}' 'in' 'i;' exp { LetExp (fst $2) () $5 $9 () }
  | 'case' exp 'of' 'i{' sep1(exp_case, 'i;') 'i}'
    { CaseExp $2 $5 () }
  | 'model' 'i{' sep1(model_subcase , 'i;') 'i}' { ModelExp $3 () }
  | non_let_case_exp { $1 }
  | 'if' exp 'then' exp 'else' exp
    { IfExp $2 $4 $6 () }
  | '\\' list(arg_pattern) '->' exp { FunExp (FunCase $2 $4) () }

non_let_case_exp :: { Exp Raw }
  : non_let_case_exp OP unary_op_exp { OpExp Enabled (Just $1) (fst $2) $3 }
  | non_let_case_exp '-' unary_op_exp { OpExp Enabled (Just $1) (T.pack "-") $3 }
  | non_let_case_exp '::' typ { SigExp $1 $3 }
  | unary_op_exp { $1 }

unary_op_exp :: { Exp Raw }
  : '-' non_op_exp { OpExp Enabled Nothing (T.pack "-") $2 }
  | non_op_exp { $1 }

non_op_exp :: { Exp Raw }
  : non_op_exp atomic_exp { applyExp $1 [$2] }
  | atomic_exp { $1 }

atomic_exp :: { Exp Raw }
  : IDENT { NameExp (LocalName (fst $1)) () }
  | CONIDENT { NameExp (CtorName (fst $1)) () }
  | '(' sep(exp,',') ')'  { exp_parens $2 }
  | '[' sep(exp, ',') ']' { ListExp Enabled $2 }
  | INTEGER { LiteralExp (IntegerLit (fst $1)) () }
  | RATIONAL { LiteralExp (RationalLit (fst $1)) () }

filename :: { Filename }
  : STR_LIT { FileStringLit (fst $1) }
  | IDENT { FileVarName (fst $1) }

source_exp :: { SourceExp Raw }
  : 'read' filename 'as' IDENT { FileSrcExp $2 (fst $4) () }
  | arg_srcexp { $1 }
  | CONIDENT list(arg_srcexp) { CtorSrcExp (fst $1) $2 () }

arg_srcexp :: { SourceExp Raw }
  : 'source' IDENT { BoundVarSrcExp (fst $2) () }
  | IDENT { VarSrcExp (fst $1) () }
  | '_' { WildSrcExp () }
  | '(' sep(source_exp,',') ')' { srcexp_parens $2 }
  | '[' source_exp '|' sep(lcomp_arm,'|') ']' { ListCompSrcExp $2 $4 () }
  | INTEGER { LiteralSrcExp (IntegerLit (fst $1)) () }
  | RATIONAL { LiteralSrcExp (RationalLit (fst $1)) () }

lcomp_arm :: { ListCompArm Raw }
  : arg_pattern '<-' gen_exp { ListCompArm $1 $3 }

typ :: { TypeP RawType }
  : typ '->' non_arrow_typ
    {
      -- We have to be left-recursive to make Happy happy (pun intended), but
      -- the arrow type associates to the right, so we do a fix-up here
      let (arg_tps, last_arg_tp) = matchArrowType $1 in
      mkArrowType (arg_tps ++ [last_arg_tp]) $3
    }
  | non_arrow_typ { $1}

non_arrow_typ :: { TypeP RawType }
  : 'Dist' atomic_typ { DistType $2 }
  | CONIDENT list(atomic_typ) { ADTType (fst $1) $2 }
  | non_ctor_atomic_typ { $1 }

-- This supports constructors not applied to any arguments, which can show up in
-- arguments of other type constructs but not as an alternate case in
-- non_arrow_typ, above, since that would cause reduce/reduce conflicts
atomic_typ :: { TypeP RawType }
  : CONIDENT { ADTType (fst $1) [] }
  | non_ctor_atomic_typ { $1 }

non_ctor_atomic_typ :: { TypeP RawType }
  : IDENT { VarType (fst $1) }
  | '[' typ ']' { ADTType (T.pack "ListF") [$2] }
  | '(' sep(typ,',') ')' { type_parens $2 }


-- Utilities -------------------------------------------------------------------

opt(p) :: { Maybe p }
  : {- empty -} { Nothing }
  | p           { Just $1 }

list(p) :: { [p] }
  : {- empty -}  { []         }
  | list_rev1(p) { reverse $1 }

list1(p) :: { [p] }
  : list_rev1(p) { reverse $1 }

list_rev1(p) :: { [p] }
  : p              { [$1]    }
  | list_rev1(p) p { $2 : $1 }

sep(p,q) :: { [p] }
  : {- empty -}  { []         }
  | sep_rev(p,q) { reverse $1 }

sep1(p,q) :: { [p] }
  : sep_rev(p,q) { reverse $1 }

sep_rev(p,q) :: { [p] }
  : p                { [$1]    }
  | sep_rev(p,q) q p { $3 : $1 }

{

type Parse = Either ParseError

data ParseError = ParseError (Maybe SourcePos) String
                  deriving (Show)

lexLayout :: SourcePos -> String -> [Lexeme Token]
lexLayout start = layout l . lexer start
  where l = Layout
             { beginsLayout = begins
             , endsLayout   = ends
             , sep          = Lexeme T.empty TInSep
             , start        = Lexeme T.empty TInStart
             , end          = Lexeme T.empty TInEnd
             }
        begins (TKeyword k) = k `elem` [K_equals, K_model, K_fun, K_of]
        begins _            = False
        ends (TKeyword K_in) = True
        ends _               = False
        --debug tokens = trace (show $ map lexemeToken tokens) $ tokens

parseError :: [Lexeme Token] -> Parse a
parseError (tok:_) = Left (ParseError (Just (sourceFrom (lexemeRange tok)))
                                      (show (lexemeToken tok)))
parseError []      = Left (ParseError Nothing "")

pattern KW k loc <- Lexeme { lexemeToken = TKeyword k, lexemeRange = loc }

parseDecls :: SourcePos -> String -> Parse [Decl Raw]
parseDecls start str = decls (lexLayout start str)

parseGPrior :: SourcePos -> String -> Parse (GPriorStmt Raw)
parseGPrior start str = gprior (lexLayout start str)

-- | Check that all 'FunCase's in a list use the same identifier, and then
-- combine them into a single 'FunDecl'
combine_fun_cases :: Maybe (TopTypeP RawType) ->
                     [(Ident, FunCase Raw)] -> Decl Raw
combine_fun_cases annot cases =
  let ident = fst (head cases) in
  if all ((==) ident . fst) cases then
    FunDecl ident annot (map snd cases)
  else error ("Incorrect head symbol in case for " ++ show ident)


-- | Match a lexeme as an identifier
matchIdent :: Lexeme Token -> Maybe (T.Text, SourceRange)
matchIdent (Lexeme { lexemeToken = TIdent txt, lexemeRange = r }) =
  Just (txt, r)
matchIdent _ = Nothing

-- | Match a lexeme as a capitalized identifier
matchConIdent :: Lexeme Token -> Maybe (T.Text, SourceRange)
matchConIdent (Lexeme { lexemeToken = TConIdent txt, lexemeRange = r }) =
  Just (txt, r)
matchConIdent _ = Nothing

-- | Match a lexeme as an operator
matchOp :: Lexeme Token -> Maybe (T.Text, SourceRange)
matchOp (Lexeme { lexemeToken = TOp txt, lexemeRange = r }) =
  Just (txt, r)
matchOp _ = Nothing

-- | Match a lexeme as an integer
matchInt :: Lexeme Token -> Maybe (Integer, SourceRange)
matchInt (Lexeme { lexemeToken = TInt i, lexemeRange = r }) =
  Just (i, r)
matchInt _ = Nothing

-- | Match a lexeme as a rational
matchRat :: Lexeme Token -> Maybe (Rational, SourceRange)
matchRat (Lexeme { lexemeToken = TRat x, lexemeRange = r }) =
  Just (x, r)
matchRat _ = Nothing

-- | Match a lexeme as a rational
matchStrLit :: Lexeme Token -> Maybe (T.Text, SourceRange)
matchStrLit (Lexeme { lexemeToken = TStrLit x, lexemeRange = r }) =
  Just (x, r)
matchStrLit _ = Nothing


-- | Smart constructor for 'TupleExp'
exp_parens :: [Exp Raw] -> Exp Raw
exp_parens [] = TupleExp [] ()
exp_parens [arg] = ParensExp Enabled arg
exp_parens args = TupleExp args ()

-- | Smart constructor for 'TupleVExp'
vexp_parens :: [VExp Raw] -> VExp Raw
vexp_parens [] = TupleVExp [] ()
vexp_parens [arg] = arg
vexp_parens args = TupleVExp args ()

-- | Smart constructor for 'TupleSrcExp'
srcexp_parens :: [SourceExp Raw] -> SourceExp Raw
srcexp_parens [] = TupleSrcExp [] ()
srcexp_parens [arg] = arg
srcexp_parens args = TupleSrcExp args ()

-- | Smart constructor for 'TuplePat'
patt_parens :: [Pattern Raw] -> Pattern Raw
patt_parens [] = TuplePat [] ()
patt_parens [arg] = arg
patt_parens args = TuplePat args ()

-- | Smart constructor for 'TupleType'
type_parens :: [TypeP RawType] -> TypeP RawType
type_parens [] = TupleType []
type_parens [tp] = tp
type_parens tps = TupleType tps

}
