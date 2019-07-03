{-# LANGUAGE DataKinds, TypeFamilies, EmptyDataDecls, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, StandaloneDeriving, UndecidableInstances #-}

module Language.Grappa.Frontend.FixupOps where

import qualified Language.Haskell.TH as TH

import Control.Monad.State

import Language.Grappa.Frontend.AST

--
-- Fixing Up Operator Precedence
--

-- | The lowest operator fixity, for top-level re-parsing
lowestFixity :: TH.Fixity
lowestFixity = TH.Fixity 0 TH.InfixR

-- | Test if an expression can be parsed as @e1 op1 (e2 op2 e3)@ when @op1@ has
-- fixity @fix1@ and @op2@ has fixity @fix2@. Note that we do not want parse
-- errors at this point, so a 'False' value means we will parse the other way,
-- as @(e1 op1 e2) op2 e3@, even though Haskell might technically not like it,
-- e.g., if both operators are non-associative.
fixityOrderOK :: TH.Fixity -> TH.Fixity -> Bool
fixityOrderOK (TH.Fixity i1 _) (TH.Fixity i2 _)
  | i2 > i1 = True
fixityOrderOK (TH.Fixity i1 _) (TH.Fixity i2 _)
  | i2 < i1 = False
fixityOrderOK (TH.Fixity _ TH.InfixR) (TH.Fixity _ TH.InfixR) = True
fixityOrderOK _ _ = False


-- | Class for fixing up the precedence of operators
class FixupOps f where
  fixupOps :: f ResolvedNames -> f PreTyped

instance FixupOps Name where
  fixupOps (LocalName nm) = LocalName nm
  fixupOps (GlobalName nm) = GlobalName nm
  fixupOps (CtorName nm) = CtorName nm

instance FixupOps Exp where
  fixupOps (NameExp nm ()) = NameExp (fixupOps nm) ()
  fixupOps (LiteralExp lit ()) = LiteralExp lit ()
  fixupOps (SigExp e tp) = SigExp (fixupOps e) tp
  fixupOps (AppExp f args ()) = AppExp (fixupOps f) (map fixupOps args) ()
  fixupOps (TupleExp exps ()) = TupleExp (map fixupOps exps) ()
  fixupOps e@(OpExp _ _ _ _) =
    case runState (reparse lowestFixity) (unparseFixupOps e) of
      (e_fix, []) -> e_fix
      (_, _) -> error "fixupOps: unexpected result from reparsing"
    where
      -- Unfold any nested OpExps into a list of non-OpExps and operators
      unparseFixupOps :: Exp ResolvedNames -> [Either ResGName (Exp PreTyped)]
      unparseFixupOps (OpExp _ (Just lhs) op rhs) =
        unparseFixupOps lhs ++ (Left op) : unparseFixupOps rhs
      unparseFixupOps (OpExp _ Nothing op rhs) = (Left op) : unparseFixupOps rhs
      unparseFixupOps e' = [Right $ fixupOps e']

      -- Re-parse a list of fixed-up expressions and operators by maintaining a
      -- push-back stream of terminals (operators) and non-terminals (fixed-up
      -- expressions) as well as a fixity level of the most recent operator we
      -- are to the right of
      reparse :: TH.Fixity ->
                 State [Either ResGName (Exp PreTyped)] (Exp PreTyped)
      reparse fixity = get >>= reparsePeek fixity

      -- The workhorse for reparse, above, with a peek at the input stream
      reparsePeek :: TH.Fixity -> [Either ResGName (Exp PreTyped)] ->
                     State [Either ResGName (Exp PreTyped)] (Exp PreTyped)
      reparsePeek _ [] = error "fixupOps: empty input stream in reparse"
      reparsePeek fixity ((Right lhs):(Left op):_)
        | fixityOrderOK fixity (gname_fixity op) =
          -- For an exp followed by an op where the op can go to the right,
          -- shift off the exp and op, recursively parse to get the rhs, pop the
          -- rhs off the stream, reduce, push the results back to the stream,
          -- and recursively continue to reparse
          do modify (tail . tail)
             rhs <- reparse (gname_fixity op)
             modify (Right (applyExp (NameExp (GlobalName op) ()) [lhs, rhs]) :)
             reparse fixity
      reparsePeek fixity ((Left op):_) =
        -- For an op on the top of the stack, it must be a unary op, so we do
        -- almost the same as the last case. Note that we do not check that op
        -- can go to the right of fixity, because we don't want parse errors at
        -- this point; instead, we just parse the unary expression anyway
        do modify tail
           rhs <- reparse (gname_fixity op)
           modify (Right (applyExp1 (NameExp (GlobalName op) ()) rhs) :)
           reparse fixity
      reparsePeek _ ((Right e'):_) =
        -- The base case, where we simply pop the expression and return it
        modify tail >> return e'
  fixupOps (ParensExp _ expr) = fixupOps expr
  fixupOps (LetExp n () lhs rhs ()) =
    LetExp n () (fixupOps lhs) (fixupOps rhs) ()
  fixupOps (CaseExp scrut cases ()) =
    CaseExp (fixupOps scrut) (map fixupOps cases) ()
  fixupOps (ModelExp cs ()) =
    ModelExp (map fixupOps cs) ()
  fixupOps (IfExp c t e ()) =
    IfExp (fixupOps c) (fixupOps t) (fixupOps e) ()
  fixupOps (ListExp _ es) =
    foldr go nil (map fixupOps es)
      where go x xs = AppExp cons [x, xs] ()
            nil = NameExp (CtorName nilInfo) ()
            cons = NameExp (CtorName consInfo) ()
            nilInfo = buildADTCtorInfo listTypeNameInfo listTypeNil
            consInfo = buildADTCtorInfo listTypeNameInfo listTypeCons
  fixupOps (FunExp fc ()) = FunExp (fixupOps fc) ()

instance FixupOps VExp where
  fixupOps (VarVExp var is_bound ()) = VarVExp var is_bound ()
  fixupOps (WildVExp ()) = WildVExp ()
  fixupOps (SigVExp vexp tp) = SigVExp (fixupOps vexp) tp
  fixupOps (CtorVExp ctor vexps ()) = CtorVExp ctor (map fixupOps vexps) ()
  fixupOps (TupleVExp vexps ()) = TupleVExp (map fixupOps vexps) ()
  fixupOps (EmbedVExp expr ()) = EmbedVExp (fixupOps expr) ()

instance FixupOps SourceExp where
  fixupOps (VarSrcExp var ()) = VarSrcExp var ()
  fixupOps (BoundVarSrcExp var ()) = BoundVarSrcExp var ()
  fixupOps (WildSrcExp ()) = WildSrcExp ()
  fixupOps (LiteralSrcExp lit ()) = LiteralSrcExp lit ()
  fixupOps (CtorSrcExp ctor es ()) = CtorSrcExp ctor (map fixupOps es) ()
  fixupOps (TupleSrcExp es ()) = TupleSrcExp (map fixupOps es) ()
  fixupOps (FileSrcExp path fmt ()) = FileSrcExp path fmt ()
  fixupOps (ListCompSrcExp expr arms ()) =
    ListCompSrcExp (fixupOps expr) (map fixupOps arms) ()

instance FixupOps ListCompArm where
  fixupOps (ListCompArm pat gen) = ListCompArm (fixupOps pat) (fixupOps gen)

instance FixupOps GenExp where
  fixupOps (VarGenExp n ()) = VarGenExp n ()
  fixupOps (BoundVarGenExp n ()) = BoundVarGenExp n ()
  fixupOps (FileGenExp path fmt ()) = FileGenExp path fmt ()
  fixupOps (RangeGenExp n m s ()) = RangeGenExp n m s ()

instance FixupOps ExpCase where
  fixupOps (ExpCase patt body () ()) =
    ExpCase (fixupOps patt) (fixupOps body) () ()

instance FixupOps StmtCase where
  fixupOps (StmtCase patt body ()) =
    StmtCase (fixupOps patt) (fixupOps body) ()

instance FixupOps Stmt where
  fixupOps ReturnStmt = ReturnStmt
  fixupOps (SampleStmt vexp rhs body) =
    SampleStmt (fixupOps vexp) (fixupOps rhs) (fixupOps body)
  fixupOps (LetStmt var rhs body) =
    LetStmt var (fixupOps rhs) (fixupOps body)
  fixupOps (CaseStmt scrut cases) =
    CaseStmt (fixupOps scrut) (map fixupOps cases)

instance FixupOps GPriorStmt where
  fixupOps (GPriorStmt vexp rhs) =
    GPriorStmt (fixupOps vexp) (fixupOps rhs)

instance FixupOps Pattern where
  fixupOps (VarPat var ()) = VarPat var ()
  fixupOps (WildPat ()) = WildPat ()
  fixupOps (CtorPat ctor patts ()) =
    CtorPat ctor (map fixupOps patts) ()
  fixupOps (TuplePat patts ()) = TuplePat (map fixupOps patts) ()
  fixupOps (LitPat lit ()) = LitPat lit ()
  fixupOps (SigPat patt tp) = SigPat (fixupOps patt) tp

instance FixupOps ModelCase where
  fixupOps (ModelCase patt e body) =
    ModelCase (fixupOps patt) (fixupOps e) (fixupOps body)

instance FixupOps FunCase where
  fixupOps (FunCase patts body) = FunCase (map fixupOps patts) (fixupOps body)

instance FixupOps Decl where
  fixupOps (FunDecl nm annot cases) =
    FunDecl nm annot (map fixupOps cases)
  fixupOps (SourceDecl name tp sexp) =
    SourceDecl name tp (fixupOps sexp)
  fixupOps (MainDecl gprior method) =
    MainDecl (fixupOps gprior) (fixupOps method)

instance FixupOps AppliedInfMethod where
  fixupOps (AppliedInfMethod name params) =
    AppliedInfMethod name (map fixupOps params)
