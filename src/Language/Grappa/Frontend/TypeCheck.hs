{-# LANGUAGE DataKinds, TypeFamilies, EmptyDataDecls, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, TemplateHaskell #-}
{-# LANGUAGE ParallelListComp #-}

module Language.Grappa.Frontend.TypeCheck where

import Data.Maybe
import System.IO

import qualified Language.Haskell.TH as TH

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except

import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.IngestEmitType
import Language.Grappa.Interp
import Language.Grappa.Inference


--
-- * Type Errors
--

data TypeErrorContext = ErrorCtxExp (Exp PreTyped) (Maybe Type)
                      | ErrorCtxVExp (VExp PreTyped) (Maybe Type)
                      | ErrorCtxSourceExp (SourceExp PreTyped) (Maybe Type)
                      | ErrorCtxGenExp (GenExp PreTyped) (Maybe Type)
                      | ErrorCtxStmt (Stmt PreTyped) (Maybe ())
                      | ErrorCtxGPStmt (GPriorStmt PreTyped) (Maybe ())
                      | ErrorCtxPattern (Pattern PreTyped) (Maybe Type)
                      | ErrorCtxVPattern (Pattern PreTyped) (Maybe Type)
                      | ErrorCtxDecl (Decl PreTyped) (Maybe ())
                      | ErrorCtxUnify Type Type
                      deriving Show

-- | This class indicates that a type @a@ has an associated constructor for
-- building 'TypeErrorContext's. The associated type @tp@ gives the type used to
-- type-check objects of type @a@, which can be 'Nothing' for type inference.
class HasErrorContext a tp | a -> tp where
  mkErrorContext :: a -> Maybe tp -> TypeErrorContext

instance HasErrorContext (Exp PreTyped) Type where
  mkErrorContext = ErrorCtxExp
instance HasErrorContext (VExp PreTyped) Type where
  mkErrorContext = ErrorCtxVExp
instance HasErrorContext (SourceExp PreTyped) Type where
  mkErrorContext = ErrorCtxSourceExp
instance HasErrorContext (GenExp PreTyped) Type where
  mkErrorContext = ErrorCtxGenExp
instance HasErrorContext (Stmt PreTyped) () where
  mkErrorContext = ErrorCtxStmt
instance HasErrorContext (GPriorStmt PreTyped) () where
  mkErrorContext = ErrorCtxGPStmt
instance HasErrorContext (Pattern PreTyped) Type where
  mkErrorContext = ErrorCtxPattern
instance HasErrorContext (Decl PreTyped) () where
  mkErrorContext = ErrorCtxDecl

data TypeError = ErrorNotEqual Type Type
               | ErrorOccurs TVar Type
               | ErrorTooGeneral TopType Type
               | ErrorCaseArity
               | ErrorCtorWrongArity CtorInfo Int
               | ErrorNotArrowType Type
               | ErrorNotTupleType Int Type
               | ErrorNotDistType Type
               | ErrorNotBaseType Type
               | ErrorNotListType Type
               | ErrorBadDeclTypeAnnot (Decl PreTyped)
               | ErrorUnsampledVar Ident
               | ErrorVarNotInScope Ident
               | ErrorUnsampledVars (Set Ident)
               | ErrorEmit EmitError
               | ErrorIngest IngestError
               | ErrorMisc String
               | ErrorContext TypeError TypeErrorContext
               deriving Show


--
-- * The Type-Checking Monad
--

-- | The type of type-checking environments, which contain:
--
-- * Maps from type variables to either their definitions, if they have any;
--
-- * A counter for creating fresh type variables;
--
-- * The current set of typeclass constraints;
--
-- * The current set of distribution types used by a computation;
--
-- * The set of variables that must be sampled from before the end of the
-- current model;
--
-- * A map assigning types to all the local (term) variables in scope; AND
--
-- * An optional 'Handle' for debugging output.
--
-- The invariant on well-formed environments is: there should be no cycles in
-- assignments to type variables; i.e., if we keep expanding the values of type
-- variables, we never get back to variables we already expanded.
data TCEnv =
  TCEnv { tc_tvar_map :: Map TVar Type,
          tc_next_tvar :: TVar,
          tc_constrs :: Set ClassConstr,
          tc_unsampled_vars :: Set Ident,
          tc_ctx :: Map Ident Type,
          tc_debug_handle :: Maybe Handle }

-- | The default, empty type-checking environment
emptyTCEnv :: Maybe Handle -> TCEnv
emptyTCEnv debugH = TCEnv { tc_tvar_map = Map.empty,
                            tc_next_tvar = TVar 1,
                            tc_constrs = Set.empty,
                            tc_unsampled_vars = Set.empty,
                            tc_ctx = Map.empty,
                            tc_debug_handle = debugH }

-- | The type-checking monad, which allows manipulations of a type-checking
-- environment and throwing 'TypeError's
type TypeCheck = StateT TCEnv (ExceptT TypeError TH.Q)

instance SubMonad Emit TypeCheck where
  embedM m = lift $ withExceptT ErrorEmit $ ExceptT $ runEmit m

instance SubMonad Ingest TypeCheck where
  embedM m = fst <$> lift (withExceptT ErrorIngest $ ExceptT $
                           runIngest emptyIngestCache m)

-- | Type-class for debugging in computations
class Monad m => TCDebuggable m where
  tcDebug :: String -> m ()

instance TCDebuggable TypeCheck where
  tcDebug str =
    do debugH <- tc_debug_handle <$> get
       case debugH of
         Just h ->
           lift $ lift $ TH.runIO
           (hPutStrLn h (showString "Debug: " str) >> hFlush h)
         Nothing -> return ()

instance Monoid w => TCDebuggable (WriterT w TypeCheck) where
  tcDebug = lift . tcDebug

instance TCDebuggable UnifyM where
  tcDebug = lift . tcDebug

-- | Run a 'TypeCheck' computation in the underlying Template Haskell monad
runTypeCheck :: Maybe Handle -> TypeCheck a -> TH.Q (Either TypeError a)
runTypeCheck debugH m = runExceptT (fst <$> runStateT m (emptyTCEnv debugH))

-- | Clear the type-checking environment
clearTCEnv :: TypeCheck ()
clearTCEnv =
  do debugH <- tc_debug_handle <$> get
     put $ emptyTCEnv debugH

-- | Add the error context information to any type errors thrown
withErrorContext :: (MonadError TypeError m, TCDebuggable m) =>
                    TypeErrorContext -> m a -> m a
withErrorContext ctx m =
  tcDebug ("Type-checking Context: " ++ show ctx) >>
  catchError m (\e -> throwError (ErrorContext e ctx))

instance MonadFreshTVar TypeCheck where
  freshTVar =
    do tvar <- tc_next_tvar <$> get
       modify (\env -> env { tc_next_tvar = nextTVar tvar })
       return tvar

-- | Lookup just the value of a type variable, if it has one
lookupTVar :: MonadState TCEnv m => TVar -> m (Maybe Type)
lookupTVar var = Map.lookup var <$> tc_tvar_map <$> get

-- | Directly set the value of a (v)type variable. This is "unsafe" in general
-- because it does not make sure that the 'TCEnv' invariants still hold; i.e.,
-- it does not do the occurs check. It is only safe when either:
--
-- 1. The caller is already doing the occurs check; or
--
-- 2. The caller is redefining a defined type variable to an equal type modulo
-- type variable definitions.
setTVarUnsafe :: MonadState TCEnv m => TVar -> Type -> m ()
setTVarUnsafe var val =
  modify $ \env -> env { tc_tvar_map = Map.insert var val $ tc_tvar_map env }

-- | Get the current set of named constraints on types
getConstrs :: TypeCheck (Set ClassConstr)
getConstrs = tc_constrs <$> get

-- | Look up the type of a (term, not type) variable, along with a flag stating
-- whether it is in the current set of unsampled variables
lookupVarType :: Ident -> TypeCheck (Maybe Type, Bool)
lookupVarType var =
  do env <- get
     return (Map.lookup var $ tc_ctx env,
             Set.member var $ tc_unsampled_vars env)

-- | Save and restore the variable context for type-checking
withLocalVarCtx :: TypeCheck a -> TypeCheck a
withLocalVarCtx m =
  do save_env <- get
     a <- m
     modify $ \env -> env { tc_ctx = tc_ctx save_env }
     return a

-- | Add a (term, not type) variable to the typing context
addVarToContext :: Ident -> Type -> TypeCheck ()
addVarToContext var tp =
  modify $ \env ->
  env { tc_ctx = Map.insert var tp (tc_ctx env) }

-- | Typing contexts for local variables
type VarCtx = [(Ident, Type)]

-- | Mark a list of variables as sampled
markSampledVars :: VarCtx -> TypeCheck ()
markSampledVars ctx =
  modify $ \env ->
  env { tc_unsampled_vars =
          foldr (Set.delete . fst) (tc_unsampled_vars env) ctx }

-- | Locally add a set of (term, not type) variables to the typing context for
-- the duration of a given 'TypeCheck' computation
withVarCtx :: VarCtx -> TypeCheck a -> TypeCheck a
withVarCtx ctx m =
  withLocalVarCtx (mapM (\(var,tp) -> addVarToContext var tp) ctx >> m)

-- | Save and restore the set of unsampled variables
withLocalUnsampledVars :: TypeCheck a -> TypeCheck a
withLocalUnsampledVars m =
  do save_env <- get
     a <- m
     modify $ \env -> env { tc_unsampled_vars = tc_unsampled_vars save_env }
     return a

-- | Locally add a set of (term, not type) variables to the typing context, also
-- seting them as the set of unsampled variables
withUnsampledVarCtx :: VarCtx -> TypeCheck a -> TypeCheck a
withUnsampledVarCtx ctx m =
  withLocalUnsampledVars $
  (modify (\env -> env { tc_unsampled_vars = Set.fromList (map fst ctx) }) >>
   withVarCtx ctx m)


--
-- * Instantiating Top Types
--

-- | Ensure that a given type-level constraint is satisfied
ensureClassConstr :: ClassConstr -> TypeCheck ()
ensureClassConstr constr =
  modify $ \env -> env { tc_constrs = Set.insert constr $ tc_constrs env }

-- | Ensure a normal, unary, named type constraint
ensureNamedConstr :: TH.Name -> Type -> TypeCheck ()
ensureNamedConstr nm tp = ensureClassConstr (NamedConstr (ConstrInfo nm) tp)

-- | Ensure an @Interp__XXX@ constraint
ensureNamedInterpConstr :: TH.Name -> [Type] -> TypeCheck ()
ensureNamedInterpConstr nm tps =
  ensureClassConstr (InterpConstr (ConstrInfo nm) tps)

-- | Ensure an @Interp__ADT@ constraint
ensureADTInterpConstr :: Type -> TypeCheck ()
ensureADTInterpConstr tp = zonk tp >>= helper where
  helper (ADTType nm args) =
    ensureClassConstr (InterpADTConstr nm args)
  helper bad_tp =
    error $ "ensureADTInterpConstr called on a non-ADT type:" ++ show bad_tp

-- | Ensure that a type satisfies the 'Num' constraint
ensureNumTp :: Type -> TypeCheck ()
ensureNumTp tp = ensureNamedConstr ''Num tp

-- | Ensure that a type satisfies the 'Fractional' constraint
ensureFractionalTp :: Type -> TypeCheck ()
ensureFractionalTp tp = ensureNamedConstr ''Fractional tp

-- | Ensure that the given type supports the given sort of 'Literal'
ensureTypeHasLit :: Literal -> Type -> TypeCheck ()
ensureTypeHasLit (IntegerLit _) tp = do
  ensureNumTp tp
  ensureNamedInterpConstr ''Interp__'integer [tp]
ensureTypeHasLit (RationalLit _) tp = do
  ensureFractionalTp tp
  ensureNamedInterpConstr ''Interp__'rational [tp]

-- | Ensure that the given type supports the given sort of 'Literal',
-- and that we can sensibly compare those literals.
ensureTypeHasLitEq :: Literal -> Type -> TypeCheck ()
ensureTypeHasLitEq (IntegerLit _) tp = do
  ensureNamedConstr ''Eq tp
  ensureNumTp tp
  ensureNamedInterpConstr ''Interp__'integer [tp]
  ensureNamedInterpConstr ''Interp__'eqInteger [tp]
  ensureClassConstr (InterpConstr (ConstrInfo ''Interp__'ifThenElse) [])
ensureTypeHasLitEq (RationalLit _) tp = do
  ensureNamedConstr ''Eq tp
  ensureFractionalTp tp
  ensureNamedInterpConstr ''Interp__'rational [tp]
  ensureNamedInterpConstr ''Interp__'eqRational [tp]
  ensureClassConstr (InterpConstr (ConstrInfo ''Interp__'ifThenElse) [])

-- -- | Ensure that the given type supports the 'Eq' typeclass
-- ensureTypeHasEq :: Type -> TypeCheck ()
-- ensureTypeHasEq tp = do
--   ensureNamedConstr ''Eq tp
--   ensureInterpConstr (InterpEqConstr tp)

-- | Build a 'TVRenaming' that renames the given type variables to new, fresh
-- type variables
buildTVRenaming :: [TVar] -> TypeCheck TVRenaming
buildTVRenaming vars =
  TVRenaming <$>
  foldM (\tvmap var ->
          do var' <- freshTVar
             return $ Map.insert var var' tvmap) Map.empty vars

-- | Instantiate a 'TopType' with fresh (v)type variables
instantiateTopType :: TopType -> TypeCheck ([Type], Type)
instantiateTopType (TopType tvars constrs arg_tps ret_tp) =
  do ren <- buildTVRenaming tvars
     mapM_ (ensureClassConstr . rename ren) constrs
     return (rename ren arg_tps, rename ren ret_tp)


--
-- * Monad for Type Unification (and anything else with occurs checks)
--

-- | During both unification and zonking, we maintain a set of the type
-- variables that we have expanded along the path from the root to the current
-- pair of types that we are unifying, so we can avoid the infinite regress of
-- expanding the same type variable over an over again.
type UnifyM = ReaderT TVSet TypeCheck

instance MonadFreshTVar UnifyM where
  freshTVar = lift freshTVar

-- | Run a 'UnifyM' computation in the underlying 'TypeCheck' monad, starting
-- with the empty set of expanded type variables.
runUnifyM :: UnifyM a -> TypeCheck a
runUnifyM m = runReaderT m Set.empty

-- | Run a unification computation with a type variable marked as seen
withSeenVar :: MonadReader TVSet m => TVar -> m a -> m a
withSeenVar var m = local (Set.insert var) m

-- | Test whether a type variable has already been expanded, and, if so,
-- signal an occurs check violation
occursCheck :: TVar -> UnifyM ()
occursCheck var =
  do seen_vars <- ask
     tp <- fromJust <$> lookupTVar var
     if Set.member var seen_vars
       then throwError $ ErrorOccurs var tp
       else return ()


--
-- * Type Unification
--

-- | Set the value of a type variable, doing an occurs check
setTVar :: TVar -> Type -> UnifyM ()
setTVar var (VarType var')
  | var == var'
  = throwError $ ErrorMisc $ "Setting type variable " ++ show var ++ " to itself!"
setTVar var tp_in =
  do tcDebug ("setTVar " ++ show var ++ " = " ++ show tp_in ++ "{")
     -- First, make sure var is not already set; this is just a consistency
     -- check, and should never happen during type inference, so we use
     -- Haskell's error instead of an exception
     maybe_tp <- lookupTVar var
     case maybe_tp of
       Just _ -> error "setTVar: variable already set!"
       Nothing -> return ()
     -- Now set var to the zonking of tp_in. We temporarily set var to the
     -- un-zonked tp_in to handle the case of an occurs check violation in
     -- zonking tp_in, since withSeenVar requires a defined variable.
     setTVarUnsafe var tp_in
     tp <- withSeenVar var $ zonk' tp_in
     setTVarUnsafe var tp
     lift $ tcDebug "} setTVar done"

-- | The main workhorse for unification
unify' :: Type -> Type -> UnifyM ()
unify' (VarType var_l_in) (VarType var_r_in) =
  do tcDebug ("unify' " ++ show var_l_in ++ " " ++ show var_r_in)
     -- First, do an occurs check on both variables
     occursCheck var_l_in
     occursCheck var_r_in
     -- Next, use exposeType to unfold the defs of the variables
     tp_l <- exposeType' (VarType var_l_in)
     tcDebug $ "Var " ++ show var_l_in ++ " -> " ++ show tp_l
     tp_r <- exposeType' (VarType var_r_in)
     tcDebug $ "Var " ++ show var_r_in ++ " -> " ++ show tp_r
     case (tp_l, tp_r) of
       -- If we end up with equal variables, we are done!
       (VarType var_l, VarType var_r) | var_l == var_r -> return ()
       -- If we end up with a variable on one side, set it to the other side
       (VarType var_l, _) -> setTVar var_l tp_r
       (_, VarType var_r) -> setTVar var_r tp_l
       -- If we end up with two non-variable types, unify them!
       _ -> withSeenVar var_l_in $ withSeenVar var_r_in $ unify' tp_l tp_r
unify' (VarType var) tp_r =
  do occursCheck var
     tp_l_maybe <- lookupTVar var
     case tp_l_maybe of
       Just tp_l -> withSeenVar var $ unify' tp_l tp_r
       Nothing -> setTVar var tp_r
unify' tp_l (VarType var) =
  do occursCheck var
     tp_r_maybe <- lookupTVar var
     case tp_r_maybe of
       Just tp_r -> withSeenVar var $ unify' tp_l tp_r
       Nothing -> setTVar var tp_l
unify' (BaseType nm1 args1) (BaseType nm2 args2)
  | nm1 == nm2 && length args1 == length args2
  = zipWithM_ unify' args1 args2
unify' (ADTType nm1 args1) (ADTType nm2 args2)
  | nm1 == nm2 && length args1 == length args2
  = zipWithM_ unify' args1 args2
unify' (TupleType args1) (TupleType args2)
  | length args1 == length args2
  = zipWithM_ unify' args1 args2
unify' (DistType tp_l) (DistType tp_r) =
  unify' tp_l tp_r
unify' (ArrowType dom_tp_l ran_tp_l) (ArrowType dom_tp_r ran_tp_r) =
  unify' dom_tp_r dom_tp_l >> unify' ran_tp_l ran_tp_r
unify' tp_l tp_r = throwError $ ErrorNotEqual tp_l tp_r

-- | Top-level call to unify two types
unify :: Type -> Type -> TypeCheck ()
unify tp1 tp2 =
  withErrorContext (ErrorCtxUnify tp1 tp2) $
  runUnifyM $ unify' tp1 tp2


--
-- * Zonking, i.e., removing defined type variables
--

-- | Typeclass for things that are zonk-able, where zonking means expanding all
-- defined type variables in an object
class Zonkable a where
  zonk' :: a -> UnifyM a

-- | Zonk an object in the 'TypeCheck' monad
zonk :: Zonkable a => a -> TypeCheck a
zonk a = runUnifyM $ zonk' a

instance Zonkable Type where
  zonk' tp@(VarType var) =
    do occursCheck var
       maybe_tp <- lookupTVar var
       case maybe_tp of
         Nothing -> return tp
         Just var_tp ->
           withSeenVar var $
           do ret_tp <- zonk' var_tp
              -- Memoize the lookup of var's value
              setTVarUnsafe var ret_tp
              return ret_tp
  zonk' (BaseType tn tps) = BaseType tn <$> mapM zonk' tps
  zonk' (ADTType tn tps) = ADTType tn <$> mapM zonk' tps
  zonk' (TupleType tps) = TupleType <$> mapM zonk' tps
  zonk' (DistType vtp) = DistType <$> zonk' vtp
  zonk' (ArrowType t1 t2) = liftM2 ArrowType (zonk' t1) (zonk' t2)
  -- this should never happen, though, as UnusedType is only ever
  -- created by zonking an unconstrained variable in a
  -- source-expression context
  zonk' UnusedType = return UnusedType

instance Zonkable ClassConstr where
  zonk' (NamedConstr nm tp) = NamedConstr nm <$> zonk' tp
  zonk' (InterpConstr nm tps) = InterpConstr nm <$> zonk' tps
  zonk' (InterpADTConstr nm tps) = InterpADTConstr nm <$> zonk' tps

instance (Zonkable a, Zonkable b) => Zonkable (a,b) where
  zonk' (a,b) = liftM2 (\a' b' -> (a',b')) (zonk' a) (zonk' b)

instance Zonkable a => Zonkable (Maybe a) where
  zonk' (Just a) = Just <$> zonk' a
  zonk' Nothing = return Nothing

instance Zonkable a => Zonkable [a] where
  zonk' l = mapM zonk' l

instance Zonkable (Decl Typed) where
  zonk' (FunDecl f annot cases) =
    FunDecl f annot <$> zonk' cases
  zonk' (SourceDecl f t e) =
    SourceDecl f <$> zonk' t <*> zonk' e
  zonk' (MainDecl st m) =
    MainDecl <$> zonk' st <*> zonk' m

instance Zonkable (InfMethod Typed) where
  zonk' (InfMethod n ps) =
    InfMethod n <$> mapM zonk' ps

instance Zonkable (ModelCase Typed) where
  zonk' (ModelCase patt maybe_exp body) =
    liftM3 ModelCase (zonk' patt) (zonk' maybe_exp) (zonk' body)

instance Zonkable (FunCase Typed) where
  zonk' (FunCase patts exps) =
    liftM2 FunCase (zonk' patts) (zonk' exps)

instance Zonkable (Pattern Typed) where
  zonk' (VarPat var tp) = VarPat var <$> zonk' tp
  zonk' (WildPat tp) = WildPat <$> zonk' tp
  zonk' (CtorPat ctor patts tp) =
    liftM2 (CtorPat ctor) (mapM zonk' patts) (zonk' tp)
  zonk' (TuplePat patts tp) =
    liftM2 TuplePat (mapM zonk' patts) (zonk' tp)
  zonk' (LitPat lit tp) = LitPat lit <$> zonk' tp
  zonk' (SigPat patt tp) = SigPat <$> zonk' patt <*> zonk' tp

instance Zonkable (StmtCase Typed) where
  zonk' (StmtCase patt stmt tp) =
    liftM3 StmtCase (zonk' patt) (zonk' stmt) (zonk' tp)

instance Zonkable (Stmt Typed) where
  zonk' ReturnStmt = return ReturnStmt
  zonk' (SampleStmt vexp expr stmt) =
    liftM3 SampleStmt (zonk' vexp) (zonk' expr) (zonk' stmt)
  zonk' (LetStmt var expr stmt) =
    liftM2 (LetStmt var) (zonk' expr) (zonk' stmt)
  zonk' (CaseStmt scrut cases) =
    liftM2 CaseStmt (zonk' scrut) (zonk' cases)

instance Zonkable (ExpCase Typed) where
  zonk' (ExpCase patt expr tp1 tp2) =
    liftM4 ExpCase (zonk' patt) (zonk' expr) (zonk' tp1) (zonk' tp2)

instance Zonkable (Exp Typed) where
  zonk' (NameExp nm tp) = NameExp nm <$> zonk' tp
  zonk' (LiteralExp lit tp) = LiteralExp lit <$> zonk' tp
  zonk' (SigExp e tp) = SigExp <$> zonk' e <*> zonk' tp
  zonk' (AppExp f args tp) =
    liftM3 AppExp (zonk' f) (mapM zonk' args) (zonk' tp)
  zonk' (TupleExp args tp) =
    liftM2 TupleExp (mapM zonk' args) (zonk' tp)
  zonk' (OpExp enabled _ _ _) = notEnabled enabled
  zonk' (ParensExp enabled _) = notEnabled enabled
  zonk' (ListExp enabled _) = notEnabled enabled
  zonk' (LetExp n n_tp lhs rhs tp) =
    LetExp n <$> zonk' n_tp <*> zonk' lhs <*> zonk' rhs <*> zonk' tp
  zonk' (CaseExp scrut cases tp) =
    liftM3 CaseExp (zonk' scrut) (zonk' cases) (zonk' tp)
  zonk' (ModelExp cs tp) =
    ModelExp <$> mapM zonk' cs <*> zonk' tp
  zonk' (IfExp c t e tp) =
    IfExp <$> zonk' c <*> zonk' t <*> zonk' e <*> zonk' tp
  zonk' (FunExp cs tp) =
    FunExp <$> zonk' cs <*> zonk' tp

instance Zonkable (VExp Typed) where
  zonk' (VarVExp nm is_bound tp) = VarVExp nm is_bound <$> zonk' tp
  zonk' (WildVExp tp) = WildVExp <$> zonk' tp
  zonk' (CtorVExp ctor patts tp) =
    liftM2 (CtorVExp ctor) (mapM zonk' patts) (zonk' tp)
  zonk' (TupleVExp patts tp) =
    liftM2 TupleVExp (mapM zonk' patts) (zonk' tp)
  zonk' (EmbedVExp expr tp) =
    liftM2 EmbedVExp (zonk' expr) (zonk' tp)
  zonk' (SigVExp expr tp) =
    SigVExp <$> zonk' expr <*> zonk' tp


instance Zonkable (GPriorStmt Typed) where
  zonk' (GPriorStmt src ee) =
    GPriorStmt <$> zonk' src <*> zonk' ee

-- | For things that might get read from a source, we want to fill
--   in otherwise unbound variables with an 'Unused' type. This should
--   only ever come up in bindings or signatures, and never in values.
zonkWithUnused :: Type -> UnifyM Type
zonkWithUnused (VarType var) =
  do occursCheck var
     maybe_tp <- lookupTVar var
     case maybe_tp of
       Nothing -> return UnusedType
       Just var_tp ->
         withSeenVar var $
         do ret_tp <- zonkWithUnused var_tp
            -- Memoize the lookup of var's value
            setTVarUnsafe var ret_tp
            return ret_tp
zonkWithUnused (BaseType tn tps) = BaseType tn <$> mapM zonkWithUnused tps
zonkWithUnused (ADTType tn tps) = ADTType tn <$> mapM zonkWithUnused tps
zonkWithUnused (TupleType tps) = TupleType <$> mapM zonkWithUnused tps
zonkWithUnused (DistType vtp) = DistType <$> zonkWithUnused vtp
zonkWithUnused (ArrowType t1 t2) = liftM2 ArrowType (zonkWithUnused t1) (zonkWithUnused t2)
  -- this should never happen, though, as UnusedType is only ever
  -- created by zonking an unconstrained variable in a
  -- source-expression context
zonkWithUnused UnusedType = return UnusedType

instance Zonkable (SourceExp Typed) where
  zonk' (VarSrcExp nm tp) = VarSrcExp nm <$> zonk' tp
  zonk' (BoundVarSrcExp n tp) = BoundVarSrcExp n <$> zonk' tp
  zonk' (WildSrcExp tp) = WildSrcExp <$> zonk' tp
  zonk' (LiteralSrcExp lit tp) =
    LiteralSrcExp lit <$> zonk' tp
  zonk' (CtorSrcExp ctor patts tp) =
    liftM2 (CtorSrcExp ctor) (mapM zonk' patts) (zonk' tp)
  zonk' (TupleSrcExp patts tp) =
    liftM2 TupleSrcExp (mapM zonk' patts) (zonk' tp)
  zonk' (FileSrcExp n f tp) =
    FileSrcExp n f <$> zonkWithUnused tp
  zonk' (ListCompSrcExp e a t) =
    ListCompSrcExp <$> zonk' e <*> zonk' a <*> zonkWithUnused t

instance Zonkable (ListCompArm Typed) where
  zonk' (ListCompArm pat ge) =
    ListCompArm <$> go pat <*> zonk' ge
    where
      go (VarPat n tp) = VarPat n <$> zonkWithUnused tp
      go (WildPat tp) = WildPat <$> zonkWithUnused tp
      go (CtorPat ctor patts tp) =
        liftM2 (CtorPat ctor) (mapM go patts) (zonkWithUnused tp)
      go (TuplePat patts tp) =
        liftM2 TuplePat (mapM go patts) (zonkWithUnused tp)
      -- Neither literals nor patterns with explicit signatures
      -- should ever be 'unused'
      go (LitPat lit tp) = LitPat lit <$> zonk' tp
      go (SigPat patt tp) = SigPat <$> zonk' patt <*> zonk' tp

instance Zonkable (GenExp Typed) where
  zonk' (VarGenExp n tp) = VarGenExp n <$> zonkWithUnused tp
  zonk' (BoundVarGenExp n tp) = BoundVarGenExp n <$> zonkWithUnused tp
  zonk' (FileGenExp n fmt tp) = FileGenExp n fmt <$> zonkWithUnused tp
  zonk' (RangeGenExp a b c tp) = RangeGenExp a b c <$> zonkWithUnused tp


--
-- * Type Exposure
--

-- | The underlying version of 'exposeType', in the 'UnifyM' monad
exposeType' :: Type -> UnifyM Type
exposeType' tp@(VarType var) =
  do occursCheck var
     tp_maybe <- lookupTVar var
     case tp_maybe of
       Nothing -> return tp
       Just var_tp -> withSeenVar var $ exposeType' var_tp
exposeType' tp = return tp

-- | Expose a type and ensure that it matches a pattern, given by the function
-- @patt@, returning the result of this pattern. If the type is a type variable,
-- then run the computation @gen_tp@, which generates a fresh type, and then
-- match that result using the pattern function @patt@.
exposeAndMatchType :: (Type -> TypeCheck a) -> TypeCheck Type -> Type ->
                      TypeCheck a
exposeAndMatchType patt gen_tp tp =
  runUnifyM $
  do tp_exposed <- exposeType' tp
     case tp_exposed of
       VarType var ->
         do fresh_tp <- lift gen_tp
            setTVar var fresh_tp
            lift $ patt fresh_tp
       _ -> lift $ patt tp_exposed

-- | Expose a type and then match it as an arrow type
exposeArrowType1 :: Type -> TypeCheck (Type, Type)
exposeArrowType1 =
  exposeAndMatchType matchArrowType1 (ArrowType <$> freshType <*> freshType)
  where
    matchArrowType1 (ArrowType dom_tp ran_tp) = return (dom_tp, ran_tp)
    matchArrowType1 tp = throwError $ ErrorNotArrowType tp

-- | Expose a type and then match it as an @n@-ary arrow type, partially
-- instantiating it if necessary
exposeArrowType :: Int -> Type -> TypeCheck ([Type], Type)
exposeArrowType 0 tp = return ([], tp)
exposeArrowType n tp =
  do (dom_tp, ran_tp) <- exposeArrowType1 tp
     (dom_tps, ret_tp) <- exposeArrowType (n-1) ran_tp
     return (dom_tp:dom_tps, ret_tp)

-- | Expose a type and then match it as an @n@-ary tuple type, partially
-- instantiating it if necessary
exposeTupleType :: Int -> Type -> TypeCheck [Type]
exposeTupleType k =
  exposeAndMatchType (matchTupleType k) (TupleType <$> replicateM k freshType)
  where
    matchTupleType k' (TupleType tps) | length tps == k' = return tps
    matchTupleType k' tp = throwError $ ErrorNotTupleType k' tp

-- | Expose a type and then match it as a distribution type
exposeDistType :: Type -> TypeCheck Type
exposeDistType =
  exposeAndMatchType matchDistType (DistType <$> freshType)
  where
    matchDistType (DistType tp) = return tp
    matchDistType tp = throwError $ ErrorNotDistType tp

-- | Expose a type and then make sure it is a Grappa list type @[a]@, returning
-- the element type @a@ on success
exposeListType :: Type -> TypeCheck Type
exposeListType =
  exposeAndMatchType
  (\tp -> maybe (throwError $ ErrorNotListType tp) return $ matchListType tp)
  freshType


--
-- * Type Checking and Inference
--

-- | Captures types of objects that can have type-checking and inference
-- performed on them, relative to normal types
class TypeCheckable tp f | f -> tp where
  typeCheck' :: f PreTyped -> tp -> TypeCheck (f Typed)
  typeInfer' :: f PreTyped -> TypeCheck (f Typed, tp)

withTCErrorContext :: (MonadError TypeError m,
                       TCDebuggable m, HasErrorContext (f PreTyped) tp) =>
                      f PreTyped -> Maybe tp -> m a -> m a
withTCErrorContext e maybe_tp m =
  withErrorContext (mkErrorContext e maybe_tp) m

-- | Type-check an object, with it in the type error context
typeCheck :: (HasErrorContext (f PreTyped) tp, TypeCheckable tp f) =>
             f PreTyped -> tp -> TypeCheck (f Typed)
typeCheck obj tp =
  withTCErrorContext obj (Just tp) $ typeCheck' obj tp

-- | Infer the type of an object, with it in the type error context
typeInfer :: (HasErrorContext (f PreTyped) tp, TypeCheckable tp f) =>
             f PreTyped -> TypeCheck (f Typed, tp)
typeInfer obj =
  withTCErrorContext obj Nothing $ typeInfer' obj

-- | Type-check a 'Maybe' object
typeCheckMaybe :: (HasErrorContext (f PreTyped) tp, TypeCheckable tp f) =>
                  Maybe (f PreTyped) -> tp -> TypeCheck (Maybe (f Typed))
typeCheckMaybe (Just obj) tp = Just <$> typeCheck obj tp
typeCheckMaybe Nothing _ = return Nothing

-- Type-checking and inference for names
instance TypeCheckable Type Name where
  typeCheck' n tp =
    do (n_checked, tp') <- typeInfer' n
       unify tp' tp
       return n_checked

  typeInfer' (LocalName var) =
    do var_type <- lookupVarType var
       case var_type of
         (Just tp, False) -> return (LocalName var, tp)
         (Just _, True) -> throwError $ ErrorUnsampledVar var
         (Nothing, _) -> throwError $ ErrorVarNotInScope var
  typeInfer' (GlobalName gname) =
    do g_tp <- uncurry mkArrowType <$> instantiateTopType (gname_type gname)
       return (GlobalName gname, g_tp)
  typeInfer' (CtorName ctor) =
    do (arg_tps, ret_tp) <- instantiateTopType $ ctor_type ctor
       ensureADTInterpConstr ret_tp
       return (CtorName ctor, mkArrowType arg_tps ret_tp)

-- Type-checking and inference for expressions
instance TypeCheckable Type Exp where
  typeCheck' (NameExp n _) tp =
    do n' <- typeCheck' n tp
       return $ NameExp n' tp
  typeCheck' (LiteralExp lit _) tp =
    ensureTypeHasLit lit tp >> return (LiteralExp lit tp)
  typeCheck' (SigExp e tp') tp =
    unify tp' tp >> typeCheck' e tp'
  typeCheck' (AppExp f args _) tp =
    do (f_t, f_type) <- typeInfer f
       (arg_types, ret_type) <- exposeArrowType (length args) f_type
       args_t <- zipWithM typeCheck args arg_types
       unify ret_type tp
       return $ AppExp f_t args_t ret_type
  typeCheck' (TupleExp exps _) tp =
    do exp_types <- exposeTupleType (length exps) tp
       exps_t <- zipWithM typeCheck exps exp_types
       return $ TupleExp exps_t tp
  typeCheck' (OpExp enabled _ _ _) _ = notEnabled enabled
  typeCheck' (ParensExp enabled _) _ = notEnabled enabled
  typeCheck' (ListExp enabled _) _ = notEnabled enabled
  typeCheck' (LetExp n _ lhs rhs _) tp =
    do (lhs_t, n_tp) <- typeInfer lhs
       rhs_t <- withVarCtx [(n,n_tp)] $ typeCheck rhs tp
       return (LetExp n n_tp lhs_t rhs_t tp)
  typeCheck' (CaseExp scrut cases _) tp =
    do (scrut_t, match_type) <- typeInfer scrut
       cases_t <- mapM (\c -> typeCheck' c (match_type, tp)) cases
       ensureADTInterpConstr match_type
       return $ CaseExp scrut_t cases_t tp
  typeCheck' (ModelExp cs _) tp = do
    vtp <- exposeDistType tp
    cs' <- mapM (flip typeCheck' vtp) cs
    ensureModelExpConstraints cs'
    return (ModelExp cs' (DistType vtp))
  typeCheck' (IfExp c t e _) tp = do
    c_t <- typeCheck c boolType
    t_t <- typeCheck t tp
    e_t <- typeCheck e tp
    ensureClassConstr (InterpConstr (ConstrInfo ''Interp__'ifThenElse) [])
    return (IfExp c_t t_t e_t tp)
  typeCheck' (FunExp (FunCase pats e) _) tp = do
    (args_tp, ret_tp) <- exposeArrowType (length pats) tp
    (pats_t, var_ctxs) <- unzip <$> zipWithM typeCheckPatt pats args_tp
    e_t <- withVarCtx (concat var_ctxs) $ typeCheck e ret_tp
    return (FunExp (FunCase pats_t e_t) tp)

  typeInfer' (NameExp n _) =
    (\(n', tp) -> (NameExp n' tp, tp)) <$> typeInfer' n
  typeInfer' (LiteralExp lit _) =
    do tp <- freshType
       ensureTypeHasLit lit tp
       return (LiteralExp lit tp, tp)
  typeInfer' (SigExp e tp') =
    do e_t <- typeCheck' e tp'
       return (e_t, tp')
  typeInfer' (AppExp f args _) =
    do (f_t, f_type) <- typeInfer f
       (arg_types, ret_type) <- exposeArrowType (length args) f_type
       args_t <- zipWithM typeCheck args arg_types
       return (AppExp f_t args_t ret_type, ret_type)
  typeInfer' (TupleExp exps _) =
    do (exps_t, tps) <- unzip <$> mapM typeInfer exps
       return (TupleExp exps_t (TupleType tps), TupleType tps)
  typeInfer' (OpExp enabled _ _ _) = notEnabled enabled
  typeInfer' (ParensExp enabled _) = notEnabled enabled
  typeInfer' (ListExp enabled _) = notEnabled enabled
  typeInfer' (LetExp n _ lhs rhs _) =
    do (lhs_t, n_tp) <- typeInfer lhs
       (rhs_t, tp) <- withVarCtx [(n,n_tp)] $ typeInfer rhs
       return (LetExp n n_tp lhs_t rhs_t tp, tp)
  typeInfer' (CaseExp scrut cases _) =
    do (scrut_t, match_type) <- typeInfer scrut
       ret_tp <- freshType
       cases_t <- mapM (\c -> typeCheck' c (match_type, ret_tp)) cases
       return (CaseExp scrut_t cases_t ret_tp, ret_tp)
  typeInfer' (ModelExp (c:cs) _) = do
    (fst_subcase_t, vtp) <- typeInfer' c
    subcases_t <- mapM (flip typeCheck' vtp) cs
    ensureModelExpConstraints (fst_subcase_t : subcases_t)
    return (ModelExp (fst_subcase_t : subcases_t) (DistType vtp), (DistType vtp))
  typeInfer' (ModelExp [] _) =
    error "Empty list of sub-cases!"
  typeInfer' (IfExp c t e _) = do
    c_t <- typeCheck c boolType
    (t_t, tp) <- typeInfer t
    e_t <- typeCheck e tp
    ensureClassConstr (InterpConstr (ConstrInfo ''Interp__'ifThenElse) [])
    return (IfExp c_t t_t e_t tp, tp)
  typeInfer' (FunExp (FunCase pats e) _) = do
    patsInf <- mapM typeInferPatt pats
    let (pats_t, pat_typs, var_ctxs) = unzip3 patsInf
    (e_t, e_typ) <- withVarCtx (concat var_ctxs) $ typeInfer e
    let tp = foldr ArrowType e_typ pat_typs
    return (FunExp (FunCase pats_t e_t) tp, tp)


-- Type-checking and inference for statements
instance TypeCheckable () Stmt where
  typeCheck' ReturnStmt () =
    do unsampled_vars <- tc_unsampled_vars <$> get
       if Set.null unsampled_vars then return ReturnStmt else
         throwError $ ErrorUnsampledVars unsampled_vars
  typeCheck' (SampleStmt vexp dist_exp body_exp) () =
    do
      -- First, infer the type of the distribution
      (dist_exp_t, dist_exp_type) <- typeInfer dist_exp
      -- Next, make sure it has a distribution type
      vtp <- exposeDistType dist_exp_type
      -- Now type-check the left-hand side against the distribution type,
      -- getting both the checked left-hand side as well as the context of all
      -- variables bound by it (some of which may shadow existing variables, in
      -- which case they move from "unsampled" to "sampled")
      (vexp_t, vctx) <- typeCheckVExp vexp vtp
      -- Mark the lhs variables as sampled
      markSampledVars vctx
      -- Finally, check the body relative to vctx
      body_exp_t <- withVarCtx vctx $ typeCheck body_exp ()
      return $ SampleStmt vexp_t dist_exp_t body_exp_t
  typeCheck' (LetStmt var rhs_exp body_exp) () =
    do
      (rhs_exp_t, var_type) <- typeInfer rhs_exp
      body_exp_t <- withVarCtx [(var,var_type)] $ typeCheck body_exp ()
      return $ LetStmt var rhs_exp_t body_exp_t
  typeCheck' (CaseStmt scrut cases) () =
    do (scrut_t, match_type) <- typeInfer scrut
       cases_t <- mapM (\c -> typeCheck' c match_type) cases
       void (error ("FIXME HERE: in type-checking case statements, "
                    ++ "should reset the sampled vars in each branch"))
       return $ CaseStmt scrut_t cases_t

  typeInfer' stmt =
    do stmt_t <- typeCheck' stmt ()
       return (stmt_t, ())


-- Type-checking and inference for gprior statements
instance TypeCheckable () GPriorStmt where
  typeCheck' (GPriorStmt lhs rhs) () =
    do
      -- First, infer the type of the distribution
      (rhs_t, rhs_type) <- typeInfer rhs
      -- Next, make sure it has a distribution type
      vtp <- exposeDistType rhs_type
      -- Now type-check the left-hand side against the distribution type
      lhs_t <- typeCheck lhs vtp
      -- Finally, check the body in ctx, with the vars in vctx marked as sampled
      zonk $ GPriorStmt lhs_t rhs_t

  typeInfer' stmt =
    do stmt_t <- typeCheck' stmt ()
       return (stmt_t, ())

instance TypeCheckable Type SourceExp where
  typeInfer' _ =
    error "Type inference not supported for source expressions!"

  typeCheck' (VarSrcExp x _) tp =
    -- NOTE: x could refer to a Haskell variable, instead of a Grappa variable,
    -- and it might even be a local Haskell variable, in which case TH cannot
    -- tell us its type (because it depends on the splice we are building!), so
    -- we defer type-checking variables and let GHC do it. This is also part of
    -- why we don't do type inference for source expressions (though we could
    -- probably hack it if we needed to with existential, instead of universal,
    -- Grappa type variables...)
    return $ VarSrcExp x tp
  typeCheck' (BoundVarSrcExp x ()) tp = do
    -- Unlike 'VarSrcExp', a 'BoundVarSrcExp' refers to a variable
    -- bound by some outer scope, probably a list comprehension.
    var_type <- lookupVarType x
    case var_type of
      (Just var_tp, _) -> do
        unify tp var_tp
        return (BoundVarSrcExp x tp)
      (Nothing, _) -> do
        return (BoundVarSrcExp x tp)
  typeCheck' (WildSrcExp _) tp =
    return $ WildSrcExp tp
  typeCheck' (LiteralSrcExp lit _) tp =
    ensureTypeHasLit lit tp >> return (LiteralSrcExp lit tp)
  typeCheck' (CtorSrcExp ctor arg_sexps _) tp =
    do (arg_tps, ret_tp) <- instantiateTopType $ ctor_type ctor
       arg_sexps_t <- zipWithM typeCheck arg_sexps arg_tps
       unify ret_tp tp
       return $ CtorSrcExp ctor arg_sexps_t ret_tp
  typeCheck' (TupleSrcExp sexps _) tp =
    do tps <- exposeTupleType (length sexps) tp
       sexps_t <- zipWithM typeCheck sexps tps
       return $ TupleSrcExp sexps_t tp
  typeCheck' (FileSrcExp filename fmt _) tp =
    do elem_tp <- exposeListType tp
       return $ FileSrcExp filename fmt (mkListType elem_tp)
  typeCheck' (ListCompSrcExp expr arms ()) tp = do
    elem_tp <- exposeListType tp
    arms_t <- mapM typeInferArm arms
    expr_t <- withVarCtx (concat (map snd arms_t))
                $ typeCheck expr elem_tp
    return (ListCompSrcExp expr_t (map fst arms_t) tp)

instance TypeCheckable Type GenExp where
  typeInfer' _ =
    error "Type inference not supported for generator expressions!"

  typeCheck' (VarGenExp x ()) tp = do
    return (VarGenExp x tp)
  typeCheck' (BoundVarGenExp x ()) tp = do
    var_type <- lookupVarType x
    case var_type of
      (Just var_tp, _) -> do
        unify tp var_tp
        return (BoundVarGenExp x tp)
      (Nothing, _) -> do
        return (BoundVarGenExp x tp)
  typeCheck' (FileGenExp filename fmt ()) tp = do
    elem_tp <- exposeListType tp
    return (FileGenExp filename fmt (mkListType elem_tp))
  typeCheck' (RangeGenExp n m s ()) tp = do
    return (RangeGenExp n m s tp)

-- We need to get the variable context out of an arm, and there's really
-- nothing for us to check it against
typeInferArm :: ListCompArm PreTyped -> TypeCheck (ListCompArm Typed, VarCtx)
typeInferArm (ListCompArm pat expr) = do
  (pat', pat_t, ctx) <- typeInferPatt pat
  expr' <- typeCheck expr (mkListType pat_t)
  return (ListCompArm pat' expr', ctx)


-- Type checking and inference for cases of case expressions, which are
-- type-checked against a pair of types, one for the pattern and one for the
-- return value of the case
instance TypeCheckable (Type, Type) ExpCase where
  typeCheck' (ExpCase patt body _ _) (patt_tp, body_tp) =
    do (patt_t, var_ctx) <- typeCheckPatt patt patt_tp
       body_t <- withVarCtx var_ctx $ typeCheck body body_tp
       ensurePatternConstraints patt_t
       return $ ExpCase patt_t body_t patt_tp body_tp

  typeInfer' (ExpCase patt body _ _) =
    do (patt_t, patt_tp, var_ctx) <- typeInferPatt patt
       (body_t, body_tp) <- withVarCtx var_ctx $ typeInfer body
       ensurePatternConstraints patt_t
       return (ExpCase patt_t body_t patt_tp body_tp, (patt_tp, body_tp))

-- Type checking and inference for cases of case statements, which are
-- type-checked against a single type, for the pattern, as statements always
-- have unit return type
instance TypeCheckable Type StmtCase where
  typeCheck' (StmtCase patt body _) patt_tp =
    do (patt_t, var_ctx) <- typeCheckPatt patt patt_tp
       body_t <- withVarCtx var_ctx $ typeCheck body ()
       ensurePatternConstraints patt_t
       return $ StmtCase patt_t body_t patt_tp

  typeInfer' (StmtCase patt body _) =
    do (patt_t, patt_tp, var_ctx) <- typeInferPatt patt
       body_t <- withVarCtx var_ctx $ typeCheck body ()
       ensurePatternConstraints patt_t
       return (StmtCase patt_t body_t patt_tp, patt_tp)


-- Type checking and inference for ModelCases, which are type-checked against
-- a single type for the pattern
instance TypeCheckable Type ModelCase where
  typeCheck' (ModelCase vpatt prob_exp body) vpatt_tp =
    do
      -- First, type-check the variable pattern; note that var_ctx binds
      -- distribution variables which are unsampled, so withVarCtx should be
      -- passed 'True' below for the computation that binds it
      (vpatt_t, var_ctx) <- typeCheckPatt vpatt vpatt_tp
      -- Now type-check the other components relative to var_ctx; note that the
      -- prpobability expression cannot depend on the free variables of vpatt
      liftM2 (ModelCase vpatt_t) (typeCheck prob_exp probType)
        (withUnsampledVarCtx var_ctx $ typeCheck body ())

  typeInfer' (ModelCase vpatt prob_exp body) =
    withLocalUnsampledVars $
    do
      -- First, infer the type of the variable pattern; note that var_ctx binds
      -- distribution variables which are unsampled, so withVarCtx should be
      -- passed 'True' below for the computations that bind it
      (vpatt_t, vpatt_tp, var_ctx) <- typeInferPatt vpatt
      -- Now type-check the other components relative to var_ctx; note that the
      -- prpobability expression cannot depend on the free variables of vpatt
      maybe_exp_t <- typeCheck prob_exp probType
      body_t <- withUnsampledVarCtx var_ctx $ typeCheck body ()
      return (ModelCase vpatt_t maybe_exp_t body_t, vpatt_tp)


-- | Ensure all the constraints needed to use a pattern in a case expression
ensurePatternConstraints :: Pattern Typed -> TypeCheck ()
ensurePatternConstraints (VarPat {}) = return ()
ensurePatternConstraints (WildPat {}) = return ()
ensurePatternConstraints (CtorPat _ ps t) = do
  ensureADTInterpConstr t
  mapM_ ensurePatternConstraints ps
ensurePatternConstraints (TuplePat ps _) =
  mapM_ ensurePatternConstraints ps
ensurePatternConstraints (LitPat (IntegerLit _) tp) =
  ensureNamedInterpConstr ''Interp__'integer [tp] >>
  ensureNamedInterpConstr ''Interp__'eq'eq [tp] >>
  ensureNamedInterpConstr ''Interp__'ifThenElse []
ensurePatternConstraints (LitPat (RationalLit _) tp) =
  ensureNamedInterpConstr ''Interp__'rational [tp] >>
  ensureNamedInterpConstr ''Interp__'eq'eq [tp] >>
  ensureNamedInterpConstr ''Interp__'ifThenElse []
ensurePatternConstraints (SigPat p _) =
  ensurePatternConstraints p

-- | Ensure all the constraints needed to use a pattern in a model expression
ensureVPatternConstraints :: Pattern Typed -> TypeCheck ()
ensureVPatternConstraints (VarPat {}) = return ()
ensureVPatternConstraints (WildPat {}) = return ()
ensureVPatternConstraints (CtorPat _ ps tp) =
  do mapM_ ensureVPatternConstraints ps
     ensureADTInterpConstr tp
ensureVPatternConstraints (TuplePat ps _) = mapM_ ensureVPatternConstraints ps
ensureVPatternConstraints (LitPat (IntegerLit _) tp) =
  ensureNamedInterpConstr ''Interp__'integer [tp] >>
  ensureNamedInterpConstr ''Interp__'ifThenElseStmt []
ensureVPatternConstraints (LitPat (RationalLit _) tp) =
  ensureNamedInterpConstr ''Interp__'rational [tp] >>
  ensureNamedInterpConstr ''Interp__'ifThenElseStmt []
ensureVPatternConstraints (SigPat p _) = ensureVPatternConstraints p

-- | Ensure the type constraints needed to form a model expression over the
-- given set of 'ModelCase's
ensureModelExpConstraints :: [ModelCase Typed] -> TypeCheck ()
ensureModelExpConstraints cases =
  -- First, ensure the constraints for the v-patterns in all the cases
  mapM (\(ModelCase patt _ _) -> ensureVPatternConstraints patt) cases >>
  -- For more than one case, we also need the Interp__'vmatch constraint
  if length cases > 1 then
    ensureNamedInterpConstr ''Interp__'vmatch []
  else return ()


-- Type checking and inference for FunCases, which are type-checked against a
-- list of types for the arguments and a single return type
instance TypeCheckable ([Type], Type) FunCase where
  typeCheck' (FunCase arg_patts body) (arg_tps, ret_tp)
    | length arg_tps == length arg_patts
    = do (arg_patts_t, var_ctxs) <-
           unzip <$> zipWithM typeCheckPatt arg_patts arg_tps
         body_t <- withVarCtx (concat var_ctxs) $ typeCheck body ret_tp
         mapM_ ensurePatternConstraints arg_patts_t
         return (FunCase arg_patts_t body_t)
  typeCheck' _ _ =
    throwError ErrorCaseArity

  typeInfer' (FunCase arg_patts body) =
    do (arg_patts_t, arg_tps, var_ctxs) <-
         unzip3 <$> mapM typeInferPatt arg_patts
       (body_t, ret_tp) <- withVarCtx (concat var_ctxs) $ typeInfer body
       mapM_ ensurePatternConstraints arg_patts_t
       return (FunCase arg_patts_t body_t, (arg_tps, ret_tp))


-- | Type-check a pattern, making sure that it can be used to match a value of
-- the given type. Also return any variables bound by the pattern, along with
-- their types.
typeCheckPatt :: Pattern PreTyped -> Type -> TypeCheck (Pattern Typed, VarCtx)
typeCheckPatt patt tp = runWriterT $ tcPatt patt tp

-- | The main workhorse for 'typeCheckPatt'
tcPatt :: Pattern PreTyped -> Type -> WriterT VarCtx TypeCheck (Pattern Typed)
tcPatt p t =
  withErrorContext (mkErrorContext p (Just t)) $ tcPatt' p t where
  tcPatt' :: Pattern PreTyped -> Type ->
             WriterT VarCtx TypeCheck (Pattern Typed)
  tcPatt' (VarPat var _) tp =
    tell [(var, tp)] >> return (VarPat var tp)
  tcPatt' (WildPat _) tp = return $ WildPat tp
  tcPatt' (CtorPat ctor patts _) tp =
    do
      -- First, instantiate the type of the constructor
      let ctor_top_type = ctor_type ctor
      (patt_types, ret_type) <- lift $ instantiateTopType ctor_top_type
      -- Next, make sure the ctor has the right number of arguments
      if length patts == length patt_types then return () else
        throwError $ ErrorCtorWrongArity ctor (length patts)
      -- Type-check all the arguments
      patts_t <- zipWithM tcPatt patts patt_types
      -- Now check that the return type for the constructor unifies with the
      -- required type
      lift $ unify tp ret_type
      -- Finally, return the typed pattern
      return $ CtorPat ctor patts_t ret_type
  tcPatt' (TuplePat patts _) tp =
    do patt_tps <- lift $ exposeTupleType (length patts) tp
       patts_t <- zipWithM tcPatt patts patt_tps
       return $ TuplePat patts_t (TupleType patt_tps)
  tcPatt' (LitPat lit _) tp =
    lift (ensureTypeHasLitEq lit tp) >>
    return (LitPat lit tp)
  tcPatt' (SigPat patt tp') tp =
    do patt_t <- tcPatt patt tp'
       lift $ unify tp tp'
       return patt_t

-- | Infer the most general type for a pattern, also returning any variables
-- bound by the pattern along with their types
typeInferPatt :: Pattern PreTyped -> TypeCheck (Pattern Typed, Type, VarCtx)
typeInferPatt patt = (\((p, tp), vs) ->
                       (p, tp, vs)) <$> (runWriterT $ tiPatt patt)

-- | The main workhorse for 'typeInferPatt'
tiPatt :: Pattern PreTyped -> WriterT VarCtx TypeCheck (Pattern Typed, Type)
tiPatt p =
  withErrorContext (mkErrorContext p Nothing) $ tiPatt' p where
  tiPatt' :: Pattern PreTyped -> WriterT VarCtx TypeCheck (Pattern Typed, Type)
  tiPatt' (VarPat var _) =
    do tp <- lift $ freshType
       tell [(var, tp)] >> return (VarPat var tp, tp)
  tiPatt' (WildPat _) =
    do tp <- lift $ freshType
       return (WildPat tp, tp)
  tiPatt' (CtorPat ctor patts _) =
    do
      -- First, instantiate the type of the constructor
      let ctor_top_type = ctor_type ctor
      (patt_types, ret_type) <- lift $ instantiateTopType ctor_top_type
      -- Next, make sure the ctor has the right number of arguments
      if length patts == length patt_types then return () else
        throwError $ ErrorCtorWrongArity ctor (length patts)
      -- Type-check all the arguments
      patts_t <- zipWithM tcPatt patts patt_types
      -- Finally, return the typed pattern and its type
      return (CtorPat ctor patts_t ret_type, ret_type)
  tiPatt' (TuplePat patts _) =
    do (patts_t, patt_tps) <- unzip <$> mapM tiPatt patts
       return (TuplePat patts_t (TupleType patt_tps), (TupleType patt_tps))
  tiPatt' (LitPat lit _) =
    do tp <- lift $ freshType
       lift (ensureTypeHasLitEq lit tp)
       return (LitPat lit tp, tp)
  tiPatt' (SigPat patt tp) =
    do patt_t <- tcPatt patt tp
       return (patt_t, tp)


-- | Type-check a v-expression (used on the left-hand side of a sample
-- statement), returning both the typed v-expression as well as any free
-- variables that were bound by it
typeCheckVExp :: VExp PreTyped -> Type -> TypeCheck (VExp Typed, VarCtx)
typeCheckVExp vexp tp = runWriterT $ tcVExp vexp tp

-- | The main workhorse for 'typeCheckVExp'
tcVExp :: VExp PreTyped -> Type -> WriterT VarCtx TypeCheck (VExp Typed)
tcVExp v t =
  withErrorContext (mkErrorContext v (Just t)) $ tcVExp' v t where
  tcVExp' :: VExp PreTyped -> Type -> WriterT VarCtx TypeCheck (VExp Typed)
  tcVExp' (VarVExp var is_bound _) tp =
    -- Variables could be normal expressions that got parsed as VExps, but they
    -- could be DistVar variables; the only way to know is to look at whether
    -- they are unsampled or not
    do var_type <- lift $ lookupVarType var
       case (var_type, is_bound) of
         ((Just var_tp, False), True) ->
           -- A not unsampled variable: convert to an embedded expression; since
           -- it is already bound, no need to return it in the emitted context
           do lift (unify tp var_tp)
              return (EmbedVExp (NameExp (LocalName var) var_tp) tp)
         ((Just var_tp, True), True) ->
           -- An unsampled variable: leave it as-is in the v-expression, but
           -- also emit it in the bound context so that it is marked as sampled
           do lift $ unify var_tp tp
              tell [(var, tp)]
              return $ VarVExp var is_bound tp
         ((Nothing, _), False) ->
           -- An as-yet unseen variable: mark it as a fresh variable of the
           -- required type
           tell [(var, tp)] >> return (VarVExp var is_bound tp)
         _ -> error ("tcVExp: type-checker and resolver disagree "
                     ++ "on whether a variable is bound!")
  tcVExp' (WildVExp _) tp =
    do return $ WildVExp tp
  tcVExp' (CtorVExp ctor args _) tp =
    do
      -- For ctor applications, first instantiate the type of the constructor
      let ctor_top_vtype = ctor_type ctor
      (arg_types, ret_type) <- lift $ instantiateTopType ctor_top_vtype
      -- Next, make sure the ctor has the right number of arguments
      if length args == length arg_types then return () else
        throwError $ ErrorCtorWrongArity ctor (length args)
      -- Type-check all the arguments
      args_t <- zipWithM tcVExp args arg_types
      -- Now unify the return type with the expected type
      lift $ unify ret_type tp
      -- Finally, return the typed vexp
      return $ CtorVExp ctor args_t ret_type
  tcVExp' (TupleVExp args _) tp =
    do arg_types <- lift $ exposeTupleType (length args) tp
       args_t <- zipWithM tcVExp args arg_types
       return $ TupleVExp args_t (TupleType arg_types)
  tcVExp' (EmbedVExp expr _) tp =
    do exp_t <- lift $ typeCheck expr tp
       return $ EmbedVExp exp_t tp
  tcVExp' (SigVExp expr tp') tp =
    do expr_t <- tcVExp' expr tp'
       lift $ unify tp tp'
       return $ SigVExp expr_t tp'


--
-- * Type-Checking for Top-Level Declarations
--

-- | Test if all the type variables in a set are general, meaning that they are
-- only instantiated to distinct type variables
ensureTVarsGeneral :: TopType -> Type -> TVSet -> TypeCheck ()
ensureTVarsGeneral top_tp tp tvs =
  void $ runExceptT $ flip runStateT Set.empty $
  catchError (ensureDistinct tvs)
  (\_ -> lift $ lift $
         do tp' <- zonk tp
            throwError $ ErrorTooGeneral top_tp tp')
  where
    -- Ensure that the given type variables are all mapped to distinct type
    -- variables, where a variable with no value is considered to be mapped to
    -- itself
    ensureDistinct :: TVSet -> StateT TVSet (ExceptT () TypeCheck) ()
    ensureDistinct tvset =
      forM_ tvset $ \tvar ->
      do maybe_val <- lift $ lift $ lookupTVar tvar
         dest_var <-
           case maybe_val of
             Just (VarType v) -> return v
             Just _ -> throwError ()
             Nothing -> return tvar
         used_vars <- get
         if Set.member dest_var used_vars then throwError () else return ()
         put $ Set.insert dest_var used_vars

-- | Build a 'TopType' for a type by zonking all the types, generalizing over
-- all the free type variables, and doing some simplifications
buildTopType :: [Type] -> Type -> TypeCheck TopType
buildTopType arg_tps_in ret_tp_in =
  do
    -- First, get all the components of our top type and zonk them
    arg_tps <- zonk arg_tps_in
    ret_tp <- zonk ret_tp_in
    -- Get all the constraints and zonk them
    -- FIXME: simplify type constraints by looking up instances that match the
    -- head of the type to which the constraint is applied
    constrs_in <- Set.toList <$> getConstrs
    constrs <- mapM zonk constrs_in
    let vars = freeVars (arg_tps, ret_tp)
    return $ TopType (Set.toList vars) constrs arg_tps ret_tp


instance TypeCheckable () Decl where
  typeInfer' decl =
    do decl_t <- typeCheck' decl ()
       return (decl_t, ())

  typeCheck' (FunDecl nm (Just top_tp) cases) () =
    do clearTCEnv
       (arg_tps, ret_tp) <- instantiateTopType top_tp
       let tvset = freeVars (arg_tps, ret_tp)
       cases_t <-
         -- FIXME: use the top-level type for nm here in recursive calls
         withVarCtx [(nm, mkArrowType arg_tps ret_tp)] $
         forM cases $ \c -> typeCheck' c (arg_tps, ret_tp)
       ensureTVarsGeneral top_tp (mkArrowType arg_tps ret_tp) tvset
       zonk $ FunDecl nm top_tp cases_t
  typeCheck' (FunDecl nm Nothing cases) () =
    do clearTCEnv
       arg_tps <- replicateM (funCaseArity $ head cases) freshType
       ret_tp <- freshType
       cases_t <-
         withVarCtx [(nm, mkArrowType arg_tps ret_tp)] $
         forM cases $ \c -> typeCheck' c (arg_tps, ret_tp)
       top_tp <- buildTopType arg_tps ret_tp
       zonk $ FunDecl nm top_tp cases_t
  typeCheck' (SourceDecl name tp sexp) () = do
    sd <- SourceDecl name tp <$> typeCheck sexp tp
    zonk sd
  typeCheck' (MainDecl gprior (InfMethod name args)) () = do
    gprior_tp <- typeCheck gprior ()
    params_tp <- sequence [ typeCheck' e (grappaType (ipType p))
                          | e <- args
                          | p <- imParams name
                          ]
    zonk (MainDecl gprior_tp (InfMethod name params_tp))
      where grappaType PTString = error "Grappa doesn't understand strings yet!"
            grappaType PTInt    = intType
            grappaType PTFloat  = doubleType
