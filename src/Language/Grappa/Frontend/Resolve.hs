{-# LANGUAGE DataKinds, TypeFamilies, EmptyDataDecls, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Grappa.Frontend.Resolve where

import Data.List

import qualified Data.Text as T
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Compat as THCompat

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State
import Control.Monad.Except

import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.IngestEmitType
import Language.Grappa.Inference


--
-- The Monad for Resolution
--

-- | Errors that can occur during resolution
data ResolveError = ResErrorUnbound Ident
                  | ResErrorUnboundType Ident
                  | ResErrorNotDefVar TH.Name
                  | ResErrorNotCtor TH.Name
                  | ResErrorIngest IngestError
                  deriving Show

-- | Environments for name resolution
data ResolveEnv = ResolveEnv { resolve_ingest_cache :: IngestCache,
                               resolve_tp_names :: Map Ident TVar,
                               resolve_next_tvar :: TVar,
                               resolve_gnames :: Map Ident ResGName,
                               resolve_ctors :: Map Ident CtorInfo,
                               resolve_bound_vars :: Set Ident }

resolveEnvAddGname :: Ident -> ResGName -> ResolveEnv -> ResolveEnv
resolveEnvAddGname nm gname env =
  env { resolve_gnames = Map.insert nm gname $ resolve_gnames env }

-- | The default, empty environment for resolution
emptyResolveEnv :: ResolveEnv
emptyResolveEnv =
  ResolveEnv { resolve_ingest_cache = emptyIngestCache,
               resolve_tp_names = Map.empty,
               resolve_next_tvar = firstTVar,
               resolve_gnames = Map.empty,
               resolve_ctors = Map.empty,
               resolve_bound_vars = Set.empty }

-- | The monad for resolving Grappa terms
type Resolve = StateT ResolveEnv (ExceptT ResolveError TH.Q)

-- | Memoize a computation for resolving identifiers, using getter and setter
-- methods for finding the proper maps in the environment
memoizeResolve :: (ResolveEnv -> Map Ident a) ->
                  (ResolveEnv -> Map Ident a -> ResolveEnv) ->
                  Ident -> Resolve a -> Resolve a
memoizeResolve getter setter x m =
  do maybe_res <- Map.lookup x <$> getter <$> get
     case maybe_res of
       Just res -> return res
       Nothing ->
         do res <- m
            modify $ \env -> setter env $ Map.insert x res $ getter env
            return res

-- | Run a resolution computation in the scope of some bound variables
withBoundVars :: Set Ident -> Resolve a -> Resolve a
withBoundVars vars m =
  do saved_vars <- resolve_bound_vars <$> get
     modify $ \env ->
       env { resolve_bound_vars = Set.union vars $ resolve_bound_vars env }
     res <- m
     modify $ \env -> env { resolve_bound_vars = saved_vars }
     return res

instance SubMonad TH.Q Resolve where
  embedM = lift . lift

instance SubMonad Ingest Resolve where
  embedM m =
    do icache <- resolve_ingest_cache <$> get
       err_or_res <- embedM $ runIngest icache m
       case err_or_res of
         Left err -> throwError $ ResErrorIngest err
         Right (res, icache') ->
           modify (\env -> env { resolve_ingest_cache = icache' }) >>
           return res


-- | Ingest a 'TopType' in the 'Resolve' monad
rIngestTopType :: Ident -> TH.Type -> Resolve TopType
rIngestTopType nm th_tp =
  embedM $ withName (T.unpack nm) $ ingestTopType th_tp


--
-- Name Resolution
--

-- | Resolve an identifier into a TH type variable
resolveTypeVar :: Ident -> Resolve TVar
resolveTypeVar nm =
  do env <- get
     case Map.lookup nm $ resolve_tp_names env of
       Just tvar -> return tvar
       Nothing ->
         let ret = resolve_next_tvar env in
         put (env { resolve_next_tvar = nextTVar $ resolve_next_tvar env,
                    resolve_tp_names =
                      Map.insert nm ret $ resolve_tp_names env }) >>
         return ret

-- | Resolve an identifier into a TH type name
resolveTypeName :: Ident -> Resolve TH.Name
resolveTypeName nm =
  do maybe_th_nm <- embedM $ TH.lookupTypeName $ T.unpack nm
     case maybe_th_nm of
       Just th_nm -> return th_nm
       Nothing -> throwError $ ResErrorUnboundType nm

-- | Resolve an ADT-like type into either an ADT or a base type
resolveADTOrBaseType :: Ident -> [Type] -> Resolve Type
resolveADTOrBaseType nm tps =
  do tn_res <- resolveTypeName nm
     tn <- embedM $ withName (T.unpack nm) $ ingestADTOrBaseName tn_res
     if typeNameIsADT tn then
       return $ ADTType tn tps
       else return $ BaseType tn tps

-- | Typeclass for type-level things whose names can be resolved
class TypeResolvable f where
  tpResolve :: f RawType -> Resolve (f TypedType)

instance TypeResolvable TypeP where
  tpResolve (VarType var) = VarType <$> resolveTypeVar var
  tpResolve (BaseType nm tps) =
    mapM tpResolve tps >>= resolveADTOrBaseType nm
  tpResolve (ADTType nm tps) =
    mapM tpResolve tps >>= resolveADTOrBaseType nm
  tpResolve (TupleType tps) = TupleType <$> mapM tpResolve tps
  tpResolve (DistType vtp) = DistType <$> tpResolve vtp
  tpResolve (ArrowType tp1 tp2) = liftM2 ArrowType (tpResolve tp1) (tpResolve tp2)
  tpResolve (UnusedType) = return UnusedType

instance TypeResolvable ClassConstrP where
  tpResolve (NamedConstr nm tp) =
    do th_nm <- resolveTypeName nm
       tp_res <- tpResolve tp
       return $ NamedConstr (ConstrInfo { constr_th_name = th_nm }) tp_res
  tpResolve (InterpConstr nm tps) =
    do th_nm <- resolveTypeName nm
       tp_res <- mapM tpResolve tps
       return $ InterpConstr (ConstrInfo { constr_th_name = th_nm }) tp_res
  tpResolve (InterpADTConstr nm tps) =
    do tn_res <- resolveTypeName nm
       tn <- embedM $ withName (T.unpack nm) $ ingestADTOrBaseName tn_res
       tp_res <- mapM tpResolve tps
       return $ InterpADTConstr tn tp_res

instance TypeResolvable TopTypeP where
  tpResolve (TopType vars constrs dom_tps ran_tp) =
    do constrs_res <- mapM tpResolve constrs
       dom_tps_res <- mapM tpResolve dom_tps
       ran_tp_res <- tpResolve ran_tp
       return $ TopType vars constrs_res dom_tps_res ran_tp_res

-- | Resolve a type annotation on a declaration
resolveDeclTypeAnnot :: DeclTypeAnnot Raw ->
                        Resolve (DeclTypeAnnot ResolvedNames)
resolveDeclTypeAnnot (Just top_tp) = Just <$> tpResolve top_tp
resolveDeclTypeAnnot Nothing = return Nothing


-- | Resolve an 'Ident' into a global Grappa name
resolveGName :: Ident -> Resolve ResGName
resolveGName x =
  memoizeResolve resolve_gnames (\c m -> c { resolve_gnames = m }) x $
  do
    -- Step 1: lookup the "interp__XXX" TH name
    maybe_th_nm <- embedM $ TH.lookupValueName $ T.unpack (interpIdent x)
    th_nm <- case maybe_th_nm of
      Just th_nm -> return th_nm
      Nothing -> throwError $ ResErrorUnbound x

    -- Step 2: reify the "interp__XXX" TH name to get its type
    th_info <- embedM $ TH.reify th_nm
    th_tp <-
      case th_info of
        THCompat.VarI _ tp_th _ -> return tp_th
        THCompat.ClassOpI _ tp_th _ -> return tp_th
        _ -> error "[unreachable]"
    top_tp <- rIngestTopType x th_tp

    -- Step 3: get the operator fixity of the Haskell name "XXX" if possible
    maybe_fixity <-
      embedM $ TH.recover (return Nothing) $
      do maybe_raw_th_nm <- TH.lookupValueName $ T.unpack x
         case maybe_raw_th_nm of
           Just raw_th_nm -> THCompat.reifyFixity raw_th_nm
           Nothing -> return Nothing
    let fixity = case maybe_fixity of
          Just f  -> f
          Nothing -> TH.defaultFixity

    -- Finally: return the resulting global name
    return $ ResGName { gname_ident = x,
                        gname_th_name = th_nm,
                        gname_type = top_tp,
                        gname_fixity = fixity }

-- | Resolve an 'Ident' into a constructor
resolveCtor :: Ident -> Resolve CtorInfo
resolveCtor x =
  memoizeResolve resolve_ctors (\c m -> c { resolve_ctors = m }) x $
  do maybe_th_nm <- embedM $ TH.lookupValueName $ T.unpack x
     th_nm <- case maybe_th_nm of
       Just th_nm -> return th_nm
       Nothing -> throwError $ ResErrorUnbound x
     th_info <- embedM $ TH.reify th_nm
     th_type_nm <-
       case th_info of
         THCompat.DataConI _ _ th_adt_nm -> return th_adt_nm
         _ -> throwError $ ResErrorNotCtor th_nm
     tn <- embedM $ withName (T.unpack x) $ ingestADTOrBaseName th_type_nm
     case tn_ctors tn of
       Just adt_ctors
         | Just adt_ctor <- find ((==) th_nm . adt_ctor_th_name) adt_ctors ->
           return $ buildADTCtorInfo tn adt_ctor
       Just _ ->
         error "resolveCtor: constructor not found in parent type!"
       Nothing ->
         do (_, ctors) <- embedM $ ingestBaseTypeName th_type_nm
            case find ((==) th_nm . base_ctor_th_name) ctors of
              Just base_ctor ->
                return $ buildBaseCtorInfo tn base_ctor
              Nothing ->
                error "resolveCtor: constructor not found in parent type!"


-- | Typeclass for term-level things whose names can be resolved
class Resolvable f where
  resolve :: f Raw -> Resolve (f ResolvedNames)

resolveMaybe :: Resolvable f => Maybe (f Raw) ->
                Resolve (Maybe (f ResolvedNames))
resolveMaybe (Just x) = Just <$> resolve x
resolveMaybe Nothing = return Nothing


instance Resolvable Name where
  resolve (LocalName nm) =
    -- NOTE: all lowercase names are parsed as local variables, so we have to
    -- check here if the variable is bound or not to decide what it becomes
    do is_local <- Set.member nm <$> resolve_bound_vars <$> get
       if is_local then return $ LocalName nm else
         GlobalName <$> resolveGName nm
  resolve (GlobalName _) =
    error "resolve: unexpected global name in parsed output"
  resolve (CtorName nm) = CtorName <$> resolveCtor nm


instance Resolvable Exp where
  resolve (NameExp n ()) =
    do gname <- resolve n
       return $ NameExp gname ()
  resolve (LiteralExp lit ()) = return $ LiteralExp lit ()
  resolve (SigExp e tp) =
    SigExp <$> resolve e <*> tpResolve tp
  resolve (AppExp f args ()) =
    liftM3 AppExp (resolve f) (mapM resolve args) (return ())
  resolve (TupleExp exps ()) =
    liftM2 TupleExp (mapM resolve exps) (return ())
  resolve (OpExp enabled Nothing nm rhs)
    | T.unpack nm == "-" =
      -- Special case for unary negation: resolve "negate" instead of "-", but
      -- use the fixity of "-"
      do minus_res <- resolveGName nm
         nm_res <- resolveGName (T.pack "negate")
         let nm_res_fix = nm_res { gname_fixity = gname_fixity minus_res }
         rhs_res <- resolve rhs
         return $ OpExp enabled Nothing nm_res_fix rhs_res
  resolve (OpExp enabled lhs nm rhs) =
    do lhs_res <- resolveMaybe lhs
       nm_res <- resolveGName nm
       rhs_res <- resolve rhs
       return $ OpExp enabled lhs_res nm_res rhs_res
  resolve (ParensExp enabled e) =
    ParensExp enabled <$> resolve e
  resolve (LetExp n () lhs rhs ()) =
    LetExp n () <$> resolve lhs <*>
    withBoundVars (Set.singleton n) (resolve rhs) <*> return ()
  resolve (CaseExp scrut cases ()) =
    liftM3 CaseExp (resolve scrut) (mapM resolve cases) (return ())
  resolve (ModelExp cs ()) =
    ModelExp <$> mapM resolve cs <*> return ()
  resolve (IfExp c t e ()) =
    IfExp <$> resolve c <*> resolve t <*> resolve e <*> return ()
  resolve (ListExp enabled es) =
    ListExp enabled <$> mapM resolve es
  resolve (FunExp fc ()) = FunExp <$> resolve fc <*> return ()

instance Resolvable VExp where
  resolve (VarVExp x _ ()) =
    do is_bound <- Set.member x <$> resolve_bound_vars <$> get
       return $ VarVExp x is_bound ()
  resolve (WildVExp ()) = return $ WildVExp ()
  resolve (CtorVExp nm es ()) =
    liftM3 CtorVExp (resolveCtor nm) (mapM resolve es) (return ())
  resolve (TupleVExp es ()) =
    liftM2 TupleVExp (mapM resolve es) (return ())
  resolve (SigVExp vexp tp) =
    SigVExp <$> resolve vexp <*> tpResolve tp
  resolve (EmbedVExp e ()) =
    liftM2 EmbedVExp (resolve e) (return ())

instance Resolvable SourceExp where
  -- A variable in a source expression might be bound by a list
  -- comprehension or it might be a variable in Haskell, so try
  -- looking it up first, and then resolve to a Haskell variable if
  -- that fails
  resolve (VarSrcExp x ()) =
    do is_bound <- Set.member x <$> resolve_bound_vars <$> get
       maybe_nm <- embedM $ TH.lookupValueName $ T.unpack x
       case maybe_nm of
         _ | is_bound -> return (BoundVarSrcExp x ())
         Just nm -> return (VarSrcExp nm ())
         Nothing -> throwError $ ResErrorUnbound x
  -- These shouldn't exist before this step, but this isn't yet
  -- encoded in the type or anything
  resolve (BoundVarSrcExp nm ()) =
    return (BoundVarSrcExp nm ())
  resolve (WildSrcExp ()) = return $ WildSrcExp ()
  resolve (LiteralSrcExp lit ()) = return $ LiteralSrcExp lit ()
  resolve (CtorSrcExp nm es ()) =
    liftM3 CtorSrcExp (resolveCtor nm) (mapM resolve es) (return ())
  resolve (TupleSrcExp es ()) =
    liftM2 TupleSrcExp (mapM resolve es) (return ())
  resolve (FileSrcExp x y ()) = return (FileSrcExp x y ())
  resolve (ListCompSrcExp e rs ()) = do
    rs' <- mapM resolve rs
    e'  <- withBoundVars (Set.unions $ map armVars rs) (resolve e)
    return (ListCompSrcExp e' rs' ())

instance Resolvable ListCompArm where
  resolve (ListCompArm pat gexp) =
    liftM2 ListCompArm (resolve pat) (resolve gexp)

instance Resolvable GenExp where
  resolve (VarGenExp x ()) =
  -- A variable in a generator expression might be bound by a list
  -- comprehension or it might be a variable in Haskell, so try
  -- looking it up first, and then resolve to a Haskell variable if
  -- that fails
    do is_bound <- Set.member x <$> resolve_bound_vars <$> get
       maybe_nm <- embedM $ TH.lookupValueName $ T.unpack x
       case maybe_nm of
         _ | is_bound -> return (BoundVarGenExp x ())
         Just nm -> return (VarGenExp nm ())
         Nothing -> throwError $ ResErrorUnbound x
  -- These shouldn't exist before this step, but this isn't yet
  -- encoded in the type or anything
  resolve (BoundVarGenExp nm ()) =
    return (BoundVarGenExp nm ())
  resolve (FileGenExp x y ()) =
    return (FileGenExp x y ())
  resolve (RangeGenExp n s y ()) =
    return (RangeGenExp n s y ())

instance Resolvable Stmt where
  resolve ReturnStmt = return ReturnStmt
  resolve (SampleStmt vexp expr body) =
    liftM3 SampleStmt (resolve vexp) (resolve expr)
    (withBoundVars (vexpVars vexp) $ resolve body)
  resolve (LetStmt x rhs body) =
    liftM2 (LetStmt x) (resolve rhs)
    (withBoundVars (Set.singleton x) $ resolve body)
  resolve (CaseStmt scrut cases) =
    liftM2 CaseStmt (resolve scrut) (mapM resolve cases)

instance Resolvable GPriorStmt where
  resolve (GPriorStmt vexp expr) =
    liftM2 GPriorStmt (resolve vexp) (resolve expr)

instance Resolvable ExpCase where
  resolve (ExpCase patt body () ()) =
    liftM4 ExpCase (resolve patt)
    (withBoundVars (patternVars patt) $ resolve body)
    (return ()) (return ())

instance Resolvable StmtCase where
  resolve (StmtCase patt body ()) =
    liftM3 StmtCase (resolve patt)
    (withBoundVars (patternVars patt) $ resolve body)
    (return ())

instance Resolvable RawPattern where
  resolve (VarPat x ()) = return $ VarPat x ()
  resolve (WildPat ()) = return $ WildPat ()
  resolve (CtorPat nm patts ()) =
    liftM3 CtorPat (resolveCtor nm) (mapM resolve patts) (return ())
  resolve (TuplePat patts ()) =
    liftM2 TuplePat (mapM resolve patts) (return ())
  resolve (LitPat lit ()) = return $ LitPat lit ()
  resolve (SigPat patt tp) = SigPat <$> resolve patt <*> tpResolve tp

instance Resolvable FunCase where
  resolve (FunCase patts body) =
    liftM2 FunCase (mapM resolve patts)
    (withBoundVars (Set.unions $ map patternVars patts) $ resolve body)

instance Resolvable ModelSubCase where
  resolve (ModelSubCase patt maybe_exp stmt) =
    let vars = patternVars patt in
    liftM3 ModelSubCase (resolve patt)
    (withBoundVars vars $
     case maybe_exp of
       Just e  -> Just <$> resolve e
       Nothing -> return Nothing)
    (withBoundVars vars $ resolve stmt)

instance Resolvable ModelCase where
  resolve (ModelCase patts sub_cases) =
    liftM2 ModelCase (mapM resolve patts)
    (withBoundVars (Set.unions $ map patternVars patts) $
     mapM resolve sub_cases)

instance Resolvable Decl where
  resolve (ModelDecl nm annot cases) =
    withBoundVars (Set.singleton nm) $
    liftM2 (ModelDecl nm) (resolveDeclTypeAnnot annot) (mapM resolve cases)
  resolve (FunDecl nm annot cases) =
    withBoundVars (Set.singleton nm) $
    liftM2 (FunDecl nm) (resolveDeclTypeAnnot annot) (mapM resolve cases)
  resolve (SourceDecl name tp sexp) =
    SourceDecl name <$> tpResolve tp <*> resolve sexp
  resolve (MainDecl gprior method) =
    MainDecl <$> resolve gprior <*> resolve method

instance Resolvable InfMethod where
  resolve (InfMethod name params)
    | Just method <- findMethod name
      = InfMethod method <$> mapM resolve params
    | otherwise = error ("No inference method named " ++ show name)
