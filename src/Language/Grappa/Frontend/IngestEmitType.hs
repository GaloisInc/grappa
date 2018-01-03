{-# LANGUAGE DataKinds, TypeFamilies, EmptyDataDecls, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns, TemplateHaskell #-}

module Language.Grappa.Frontend.IngestEmitType where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Compat as THCompat

import qualified Data.List as L
import Data.Maybe
import Data.Either

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State
import Control.Monad.Except

import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.DataSource (Unused)
import Language.Grappa.Model
import Language.Grappa.Interp
import Language.Grappa.Distribution
import Language.Grappa.GrappaInternals


--
-- * Helper functions for manipulating TH types
--

-- | Extract the name portion of a TH 'TyVarBndr'
thTyVarName :: TH.TyVarBndr -> TH.Name
thTyVarName (TH.PlainTV nm) = nm
thTyVarName (TH.KindedTV nm _) = nm

-- | Match a TH type as a TH type variable
matchTHTVar :: TH.Type -> Maybe TH.Name
matchTHTVar (TH.VarT var) = Just var
matchTHTVar _ = Nothing

-- | Match a list of TH types as a list of TH type variables
matchTHTVars :: [TH.Type] -> Maybe [TH.Name]
matchTHTVars [] = return []
matchTHTVars (TH.VarT var : tps) = (var :) <$> matchTHTVars tps
matchTHTVars _ = Nothing

-- | Match a list of TH types as all being of the form @f tp@
matchTHVarTypeApps :: TH.Name -> [TH.Type] -> Maybe [TH.Type]
matchTHVarTypeApps _ [] = return []
matchTHVarTypeApps nm (TH.AppT (TH.VarT nm') tp : tps)
  | nm == nm'
  = do ret_tps <- matchTHVarTypeApps nm tps
       return (tp : ret_tps)
matchTHVarTypeApps _ _ = Nothing

-- | Apply a TH type to a list of TH types
applyTHType :: TH.Type -> [TH.Type] -> TH.Type
applyTHType = foldl TH.AppT

-- | Pattern-match a TH type as an application of a TH type function to zero or
-- more TH type arguments
matchTHTypeApp :: TH.Type -> (TH.Type, [TH.Type])
matchTHTypeApp (TH.AppT tp arg) =
  let (f, args) = matchTHTypeApp tp in
  (f, args ++ [arg])
matchTHTypeApp (TH.SigT tp _) = matchTHTypeApp tp
matchTHTypeApp tp = (tp, [])

-- | Pattern-match a TH type as an application of a TH type function to at most
-- @n@ types
matchNTHTypeApps :: Int -> TH.Type -> (TH.Type, [TH.Type])
matchNTHTypeApps 0 tp = (tp, [])
matchNTHTypeApps n (TH.AppT tp arg) =
  let (f, args) = matchNTHTypeApps (n-1) tp in
  (f, arg:args)
matchNTHTypeApps n (TH.SigT tp _) = matchNTHTypeApps n tp
matchNTHTypeApps _ tp = (tp, [])

-- | Build an arrow type @tp1 -> ... -> tpn -> tp@
mkTHArrowType :: [TH.Type] -> TH.Type -> TH.Type
mkTHArrowType dom_tps ran_tp =
  foldr (\t1 t2 -> applyTHType TH.ArrowT [t1,t2]) ran_tp dom_tps

-- | Match a TH type of the form @tp1 -> ... -> tpn -> tp@, where @tp@ is either
-- @vtp -> 'Model' c tp@ or does not start with 'Model'
matchTHArrowType :: TH.Type -> ([TH.Type], TH.Type)
matchTHArrowType tp@(TH.AppT (TH.AppT TH.ArrowT _)
                     (TH.AppT (TH.AppT (TH.ConT model_tp) _) _))
  | model_tp == ''Model = ([], tp)
matchTHArrowType (TH.AppT (TH.AppT TH.ArrowT dom_tp) tp) =
  let (dom_tps, ret_tp) = matchTHArrowType tp in
  (dom_tp:dom_tps, ret_tp)
matchTHArrowType (TH.SigT tp _) = matchTHArrowType tp
matchTHArrowType (TH.AppT (TH.SigT tp1 _) tp2) = matchTHArrowType (TH.AppT tp1 tp2)
matchTHArrowType (TH.AppT (TH.AppT (TH.SigT tp1 _) tp2) tp3) =
  matchTHArrowType (TH.AppT (TH.AppT tp1 tp2) tp3)
matchTHArrowType tp = ([], tp)

-- | Match a TH type @forall a1 ... an. ctx => tp1 -> ... -> tpn -> tp@, where
-- @tp@ is either @vtp -> 'Model' c tp@ or does not start with 'Model'
matchTHTopType :: TH.Type -> ([TH.TyVarBndr], TH.Cxt, [TH.Type], TH.Type)
matchTHTopType (TH.ForallT tyvars ctx tp) =
  let (tyvars', ctx', dom_tps, ret_tp) = matchTHTopType tp in
  (tyvars++tyvars', ctx++ctx', dom_tps, ret_tp)
matchTHTopType tp =
  let (dom_tps, ret_tp) = matchTHArrowType tp in
  ([], [], dom_tps, ret_tp)

-- | Match a TH type @forall a1 .. an. ctx => GExpr repr (t1 -> .. -> tn -> t)@
-- and return @([a1,..,an], ctx, repr, [t1,..,tn], t)@
matchTHTopInterpType :: TH.Type -> Maybe ([TH.TyVarBndr], TH.Cxt, TH.Name,
                                          [TH.Type], TH.Type)
matchTHTopInterpType (TH.ForallT tyvars ctx tp) =
  do (tyvars', ctx', repr_var, dom_tps, ret_tp) <- matchTHTopInterpType tp
     return (tyvars++tyvars', ctx++ctx', repr_var, dom_tps, ret_tp)
matchTHTopInterpType (matchTHTypeApp ->
                      (TH.ConT gexpr_nm, [TH.VarT repr_var, tp]))
  | gexpr_nm == ''GExpr
  = let (dom_tps, ret_tp) = matchTHArrowType tp in
    return ([], [], repr_var, dom_tps, ret_tp)
matchTHTopInterpType _ = Nothing

-- | Substitutions for TH type variables
type THSubst = Map TH.Name TH.Type

-- | General first-order matching for TH types: if there is a substitution for
-- the free type variables of @patt@ that makes it equal @tp@, return that
-- substitution, otherwise return 'Nothing'
matchTHType :: TH.Type -> TH.Type -> Maybe THSubst
matchTHType p t = snd <$> runStateT (match' p t) Map.empty where
  match' :: TH.Type -> TH.Type -> StateT THSubst Maybe ()
  match' (TH.VarT x) tp =
    do x_tp_maybe <- Map.lookup x <$> get
       case x_tp_maybe of
         Just x_tp -> match' x_tp tp
         Nothing -> modify $ Map.insert x tp
  match' (TH.AppT patt1 patt2) (TH.AppT tp1 tp2) =
    match' patt1 tp1 >> match' patt2 tp2
  match' (TH.SigT patt _) tp = match' patt tp
  match' patt (TH.SigT tp _) = match' patt tp
  match' (TH.ConT ctor1) (TH.ConT ctor2) | ctor1 == ctor2 = return ()
  match' TH.ArrowT TH.ArrowT = return ()
  match' TH.ListT TH.ListT = return ()
  match' (TH.TupleT i) (TH.TupleT j) | i == j = return ()
  match' patt tp | patt == tp = return ()
  match' _ _ = lift Nothing

-- | Substitute for the free type variables of a TH type
substTHType :: THSubst -> TH.Type -> TH.Type
-- TODO: do we also have to avoid capture, potentially alpha-varying the forall
-- to avoid names that appear in the range of s?
substTHType s (TH.ForallT tyvars ctx tp) =
  let s' = Map.filterWithKey (\nm _ -> all ((/=) nm . thTyVarName) tyvars) s in
  TH.ForallT tyvars (map (substTHType s') ctx) (substTHType s' tp)
substTHType s (TH.SigT tp _) = substTHType s tp
substTHType s tp_x@(TH.VarT x) = Map.findWithDefault tp_x x s
-- TODO: this first `id` looks awfully suspicious. Shouldn't we be looking up
-- all these other names in the substitution, too?
substTHType s tp = THCompat.fmapType id (substTHType s) id tp

-- | Build a type-level list in TH
mkTHTypeList :: [TH.Type] -> TH.Type
mkTHTypeList [] = TH.PromotedNilT
mkTHTypeList (tp:tps) = applyTHType TH.PromotedConsT [tp, mkTHTypeList tps]

-- | Match a type-level list in TH
matchTHTypeList :: TH.Type -> Maybe [TH.Type]
matchTHTypeList TH.PromotedNilT = Just []
matchTHTypeList (matchTHTypeApp -> (TH.PromotedConsT, [tp, tps])) =
  fmap (tp :) $ matchTHTypeList tps
matchTHTypeList (TH.SigT tp _) = matchTHTypeList tp
matchTHTypeList _ = Nothing


--
-- * Emitting Types to TH
--

-- | The environments for emitting Grappa types to TH
data EmitEnv = EmitEnv { emit_var_map :: Map TVar TH.Name,
                         emit_dist_var :: TH.Name,
                         emit_repr_var :: TH.Name }

-- | The default, empty 'EmitEnv'
emptyEmitEnv :: TH.Name -> TH.Name -> EmitEnv
emptyEmitEnv c repr = EmitEnv { emit_var_map = Map.empty,
                                emit_dist_var = c,
                                emit_repr_var = repr }

-- | Errors during emitting Grappa types to TH
data EmitError = EmitErrUnknownTypeVar TVar
               deriving Show

-- | The monad for emitting Grappa types to TH
type Emit = StateT EmitEnv (ExceptT EmitError TH.Q)

-- | Run an 'Emit' computation in the 'TH.Q' monad
runEmit :: Emit a -> TH.Q (Either EmitError a)
runEmit m =
  do c_var <- TH.newName "c"
     repr_var <- TH.newName "repr"
     runExceptT $ fst <$> runStateT m (emptyEmitEnv c_var repr_var)

instance SubMonad TH.Q Emit where
  embedM = lift . lift

getDistVar :: Emit TH.Name
getDistVar = emit_dist_var <$> get

getReprVar :: Emit TH.Name
getReprVar = emit_repr_var <$> get

-- | Create a fresh TH type variable for the given Grapp type variable, and add
-- the association to the current 'Emit' computation
emitNewTVar :: TVar -> Emit TH.Name
emitNewTVar var =
  do th_var <- lift $ lift $ TH.newName "a"
     modify $ \env ->
       env { emit_var_map =
               Map.insert var th_var $ emit_var_map env }
     return th_var

-- | Emit a Grappa type variable to TH
emitTVar :: TVar -> Emit TH.Type
emitTVar var =
  do maybe_nm <- Map.lookup var <$> emit_var_map <$> get
     case maybe_nm of
       Just nm -> return $ TH.VarT nm
       Nothing -> throwError $ EmitErrUnknownTypeVar var

-- | Emit a Grappa type to TH. If the Boolean flag is 'True', emit the "interp"
-- version of the type, which uses the 'Dist' type in place of 'ModelDist'
emitType :: Bool -> Type -> Emit TH.Type
emitType _ (VarType var) = emitTVar var
emitType iflag (BaseType nm tps) =
  applyTHType (TH.ConT (tn_th_name nm)) <$> mapM (emitType iflag) tps
emitType iflag (ADTType nm tps) =
  -- Emit the type ADT (nm tps) Id
  do tps_th <- mapM (emitType iflag) tps
     return $ applyTHType (TH.ConT ''ADT)
       [applyTHType (TH.ConT (tn_th_name nm)) tps_th]
emitType iflag (TupleType tps) =
  do tps_th <- mapM (emitType iflag) tps
     embedM $ [t| ADT (TupleF $(return $ mkTHTypeList tps_th)) |]
emitType iflag (DistType tp) =
  do th_tp <- emitType iflag tp
     c_var <- emit_dist_var <$> get
     if iflag then embedM $ [t| Dist $(return th_tp) |] else
       embedM $ [t| ModelDist $(TH.varT c_var) $(return th_tp) |]
emitType iflag (ArrowType tp1 tp2) =
  applyTHType TH.ArrowT <$> mapM (emitType iflag) [tp1, tp2]
emitType _ UnusedType = return (TH.ConT ''Unused)


-- True if the type contains no type variables; false otherwise
isConcreteType :: Type -> Bool
isConcreteType t = case t of
  VarType _       -> False
  BaseType _ ts   -> all isConcreteType ts
  ADTType _ ts    -> all isConcreteType ts
  TupleType ts    -> all isConcreteType ts
  DistType _      -> True
  ArrowType t1 t2 -> isConcreteType t1 && isConcreteType t2
  UnusedType      -> True

-- True if the class constraint is over a concrete type; false
-- otherwise
isConcreteConstr :: ClassConstr -> Bool
isConcreteConstr (NamedConstr _ tp) = isConcreteType tp

-- | Emit a class constraint to TH, where the Boolean flag controls whether to
-- use the "interp" version
emitClassConstr :: Bool -> ClassConstr -> Emit TH.Type
emitClassConstr iflag (NamedConstr nm tp) =
  TH.AppT (TH.ConT $ constr_th_name nm) <$> emitType iflag tp

-- | Emit a class constraint to TH
emitClassConstrInterp :: InterpConstr -> Emit TH.Type
emitClassConstrInterp (InterpConstr nm tp) = do
  tps <- mapM (emitType True) tp
  repr <- getReprVar
  return $ foldl TH.AppT (TH.ConT $ constr_th_name nm) $ TH.VarT repr : tps
emitClassConstrInterp (InterpADTConstr nm tps) = do
  tps_th <- mapM (emitType True) tps
  repr <- getReprVar
  let nm_th = TH.ConT (tn_th_name nm)
      adt_tp_th = applyTHType nm_th tps_th
  return $ applyTHType (TH.ConT ''Interp__ADT) [TH.VarT repr, adt_tp_th]

-- | Emit a set of atomic distribution types @t1, ..., tn@ as a list of TH
-- constraints @[c t1, ..., c tn]@, where @c@ is the distribution set variable
emitDistSet :: Set Type -> Emit [TH.Type]
emitDistSet dist_set =
  do c_var <- emit_dist_var <$> get
     mapM (\tp -> TH.AppT (TH.VarT c_var) <$> emitType False tp) $
       Set.toList dist_set

-- | Emit a top-level Grappa type to TH
emitTopType :: TopType -> Emit TH.Type
emitTopType (TopType tvars constrs _ dist_set dom_tps ran_tp) =
  do c_var <- getDistVar
     tvars_th <- mapM emitNewTVar tvars
     constrs_th <-
       mapM (emitClassConstr False) (filter (not . isConcreteConstr) $
                                     L.nub constrs)
     dist_set_th <- emitDistSet dist_set
     dom_tps_th <- mapM (emitType False) dom_tps
     ran_tp_th <- emitType False ran_tp
     return $
       TH.ForallT (map TH.PlainTV $ c_var : tvars_th)
       (constrs_th ++ dist_set_th)
       (mkTHArrowType dom_tps_th ran_tp_th)

-- | Emit a top-level Grappa type to TH as an interpretation type
emitTopTypeI :: TopType -> Emit TH.Type
emitTopTypeI (TopType tvars constrs interp_constrs _ dom_tps ran_tp) =
  do tvars_th <- mapM emitNewTVar tvars
     repr <- getReprVar
     constrs_th <- mapM (emitClassConstr True) (L.nub constrs)
     interp_constrs_th <- mapM emitClassConstrInterp (L.nub interp_constrs)
     let tvar_constrs_th =
           map (TH.AppT (TH.ConT ''GrappaType) . TH.VarT) tvars_th
     let repr_c = TH.AppT (TH.ConT ''ValidRepr) (TH.VarT repr)
     let all_constrs =
           repr_c : constrs_th ++ interp_constrs_th ++ tvar_constrs_th
     tp_th <- emitType True (foldr ArrowType ran_tp dom_tps)
     return $ TH.ForallT (map TH.PlainTV (repr : tvars_th))
       all_constrs (applyTHType (TH.ConT ''GExpr) [TH.VarT repr, tp_th])


--
-- * Monad for Type Ingest
--

-- | A cache for TH type ingest, that can be saved from one ingest to the next
--
-- FIXME HERE: we do not actually use the cache yet!
data IngestCache =
  IngestCache { ingest_defined_type_names :: Map TH.Name Type,
                ingest_resolved_type_names :: Map TH.Name TypeNameInfo,
                ingest_named_constrs :: Map TH.Name ConstrInfo }

-- | The empty 'IngestCache'
emptyIngestCache :: IngestCache
emptyIngestCache =
  IngestCache { ingest_defined_type_names = Map.empty,
                ingest_resolved_type_names = Map.empty,
                ingest_named_constrs = Map.empty }

-- | How a TH type variable is being used in a Grappa type
data THTypeVarRole
  = RoleTVar TVar
    -- ^ A normal type variable
  | RoleDistSet
    -- ^ A type variable used as the first argument to the 'Model' type
  | RoleReprVar
    -- ^ A type variable used as the current representation
  deriving (Eq, Ord, Show)

-- | The environment used for TH type ingest
data IngestEnv = IngestEnv { ingest_cache :: IngestCache,
                             ingest_var_roles :: Map TH.Name THTypeVarRole,
                             ingest_next_tvar :: TVar,
                             ingest_dist_set :: Set Type }

-- | Build an ingest environment from a cache
ingestEnvFromCache :: IngestCache -> IngestEnv
ingestEnvFromCache cache =
  IngestEnv { ingest_cache = cache,
              ingest_var_roles = Map.empty,
              ingest_next_tvar = TVar 1,
              ingest_dist_set = Set.empty }

-- | Context information about ingestion errors
data IngestErrorContext = IngestCtxTopType TH.Type
                        | IngestCtxConstr TH.Type
                        | IngestCtxType TH.Type
                        | IngestCtxInterpType TH.Type
                        | IngestCtxName String
                        deriving Show

withName :: String -> Ingest a -> Ingest a
withName n = addIngestErrorContext (IngestCtxName n)

-- | Errors during TH type ingest
data IngestError = IngErrorMalformedType TH.Type
                 | IngErrorMalformedTopInterpType TH.Type
                 | IngErrorMalformedADT TH.Name
                 | IngErrorMalformedBaseType TH.Name
                 | IngErrorMalformedADTCtor TH.Con
                 | IngErrorMalformedBaseCtor TH.Con
                 | IngErrorMalformedConstr TH.Type
                 | IngErrorNonTVarAsTVar TH.Name THTypeVarRole
                 | IngErrorMultipleRoles TH.Name [THTypeVarRole]
                 | IngErrorBadDist TH.Type
                 | IngErrorUnknownSupport TH.Type
                 | IngErrorContext IngestError IngestErrorContext
                 | IngErrorNonGExpr TH.Type
                 | IngErrorMalformedInterpType TH.Type
                 | IngErrorDifferentTypes Type Type
                 deriving Show

-- | The monad for doing TH type ingest
type Ingest = StateT IngestEnv (ExceptT IngestError TH.Q)

-- | Run an 'Ingest' computation with a cache
runIngest :: IngestCache -> Ingest a ->
             TH.Q (Either IngestError (a, IngestCache))
runIngest cache m =
  runExceptT ((\(a,env) -> (a, ingest_cache env)) <$>
              runStateT m (ingestEnvFromCache cache))

-- | Add context to any ingest errors
addIngestErrorContext :: IngestErrorContext -> Ingest a -> Ingest a
addIngestErrorContext ctx m =
  catchError m (\e -> throwError (IngErrorContext e ctx))

-- | Run an 'Ingest' computation in a local, fresh environment
withLocalIngestEnv :: Ingest a -> Ingest a
withLocalIngestEnv m =
  do pre_env <- get
     ret <- m
     put pre_env
     return ret

instance MonadFreshTVar Ingest where
  freshTVar =
    do env <- get
       put $ env { ingest_next_tvar = nextTVar $ ingest_next_tvar env }
       return $ ingest_next_tvar env

-- | Get the role of a TH type variable
getTHVarRole :: TH.Name -> Ingest (Maybe THTypeVarRole)
getTHVarRole nm = Map.lookup nm <$> ingest_var_roles <$> get

-- | Set the role of a TH type variable
setTHVarRole :: TH.Name -> THTypeVarRole -> Ingest ()
setTHVarRole nm role =
  do maybe_cur_role <- getTHVarRole nm
     case maybe_cur_role of
       Just cur_role | role == cur_role -> return ()
       Just cur_role ->
         throwError $ IngErrorMultipleRoles nm [role, cur_role]
       Nothing -> return ()
     modify $ \env ->
       env { ingest_var_roles = Map.insert nm role $ ingest_var_roles env }

-- | Ensure that a TH type variable is associated with a Grappa type variable,
-- and return the Grappa type variable
getTHVarTVar :: TH.Name -> Ingest TVar
getTHVarTVar nm =
  do maybe_cur_role <- getTHVarRole nm
     case maybe_cur_role of
       Just (RoleTVar tvar) -> return tvar
       Nothing ->
         do tvar <- freshTVar
            setTHVarRole nm (RoleTVar tvar)
            return tvar
       Just role ->
         throwError $ IngErrorNonTVarAsTVar nm role

-- | Add a type to the current distribution set
addToDistSet :: Type -> Ingest ()
addToDistSet tp =
  modify $ \env -> env { ingest_dist_set =
                           Set.insert tp $ ingest_dist_set env }

-- | Call 'TH.reify' in the 'Ingest' monad
thReify :: TH.Name -> Ingest TH.Info
thReify = lift . lift . TH.reify


--
-- * Ingesting ADTs and Base Types
--

-- | Ingest a TH constructor, which should have a type of the following form:
--
-- > forall a1 ... an f r.  f tp1 -> ... -> f tpn -> T a1 ... an f r
--
-- Return the resulting ingested arguments types, along with the Grappa type
-- variables used for @r@ and the @ai@.
ingestADTCtor :: [TH.TyVarBndr] -> TH.Con -> Ingest ADTCtor
ingestADTCtor tyvars (TH.NormalC nm bang_tps)
  | (adt_vars, [f_th_var, r_th_var]) <-
      splitAt (length tyvars - 2) (map thTyVarName tyvars)
  , Just arg_th_tps <- matchTHVarTypeApps f_th_var $ map snd bang_tps
  = do args <-
         withLocalIngestEnv $
         do
           -- Make fresh type variables for the arguments of the ADT type
           r_var <- getTHVarTVar r_th_var
           tvars <- mapM getTHVarTVar adt_vars
           -- Ingest the constructor argument types
           arg_tps <- mapM ingestType arg_th_tps
           return (r_var, tvars, arg_tps)
       return $ ADTCtor { adt_ctor_th_name = nm,
                          adt_ctor_args = args }

ingestADTCtor _ con = throwError $ IngErrorMalformedADTCtor con


-- | Ingest a TH name that is supposed to refer to an ADT
ingestADTName :: TH.Name -> Ingest TypeNameInfo
ingestADTName nm =
  thReify nm >>= \th_info ->
  case th_info of
    TH.TyConI (THCompat.DataD _ _ tyvars th_ctors _) ->
      do ctors <- mapM (ingestADTCtor tyvars) th_ctors
         return $ TypeNameInfo { tn_th_name = nm,
                                 tn_arity = length tyvars - 2,
                                 tn_ctors = Just ctors }
    TH.TyConI (THCompat.NewtypeD _ _ tyvars th_ctor _) ->
      do ctor <- ingestADTCtor tyvars th_ctor
         return $ TypeNameInfo { tn_th_name = nm,
                                 tn_arity = length tyvars - 2,
                                 tn_ctors = Just [ctor] }
    _ -> throwError $ IngErrorMalformedADT nm


-- | Ingest a normal Haskell constructor as being in a "base type", i.e., in a
-- Haskell type that is somewhat external to Grappa
ingestBaseCtor :: TH.Name -> [TH.TyVarBndr] -> TH.Cxt -> TH.Con ->
                  Ingest BaseCtor
ingestBaseCtor _tp_nm tyvars ctx ctor_def =
  withLocalIngestEnv $
  do
    -- Get out the ctor name and arg types
    (ctor_nm, arg_tps_th) <-
      case ctor_def of
        TH.NormalC ctor_nm bang_tps -> return (ctor_nm, map snd bang_tps)
        TH.RecC ctor_nm var_bang_tps ->
          return (ctor_nm, map (\(_,_,tp) -> tp) var_bang_tps)
        TH.InfixC (_,tp1) ctor_nm (_,tp2) -> return (ctor_nm, [tp1,tp2])
        _ -> throwError $ IngErrorMalformedBaseCtor ctor_def
    -- Make fresh type variables for the arguments of the ADT type
    tvars <- mapM (getTHVarTVar . thTyVarName) tyvars
    -- Ingest the constraints
    constrs <- ingestConstraints ctx
    -- Ingest the constructor argument types
    arg_tps <- mapM ingestType arg_tps_th
    -- Return the results
    return $ BaseCtor { base_ctor_th_name = ctor_nm,
                        base_ctor_args = (tvars, constrs, arg_tps) }


-- | Ingest a TH name as a base type
ingestBaseTypeName :: TH.Name -> Ingest (TypeNameInfo, [BaseCtor])
ingestBaseTypeName nm = do
  th_info <- thReify nm
  case th_info of
    TH.TyConI (THCompat.DataD ctx _ tyvars th_ctors _) ->
      do ctors <- mapM (ingestBaseCtor nm tyvars ctx) th_ctors
         return (TypeNameInfo { tn_th_name = nm,
                                tn_arity = length tyvars,
                                tn_ctors = Nothing },
                 ctors)
    TH.TyConI (THCompat.NewtypeD ctx _ tyvars th_ctor _) ->
      do ctor <- ingestBaseCtor nm tyvars ctx th_ctor
         return (TypeNameInfo { tn_th_name = nm,
                                tn_arity = length tyvars,
                                tn_ctors = Nothing },
                 [ctor])
    TH.PrimTyConI _ arity _ ->
      return (TypeNameInfo { tn_th_name = nm,
                             tn_arity = arity,
                             tn_ctors = Nothing }, [])
    _ -> throwError $ IngErrorMalformedBaseType nm


-- | Ingest a TH name that could refer to a Grappa ADT or to a Haskell ADT that
-- is just a base type in Grappa
ingestADTOrBaseName :: TH.Name -> Ingest TypeNameInfo
ingestADTOrBaseName nm =
  catchError (ingestADTName nm) (\_ -> fst <$> ingestBaseTypeName nm)


--
-- * Ingesting TH Types into Grappa Types
--

-- | Ingest an application of a TH type applied to zero or more arguments
ingestTypeApp :: TH.Type -> [TH.Type] -> Ingest Type
ingestTypeApp (TH.AppT _ _) _ =
  error "ingestTypeApp: unexpected AppT constructor!"
ingestTypeApp (TH.SigT _ _) _ =
  error "ingestTypeApp: unexpected SigT constructor!"

-- Ingest types of the form @Dist c a@
ingestTypeApp (TH.ConT dist_nm) [TH.VarT model_var, th_tp]
  | dist_nm == ''ModelDist
  = do setTHVarRole model_var RoleDistSet
       tp <- ingestType th_tp
       return $ DistType tp

-- Ingest types of the form @'Dist' a@
ingestTypeApp (TH.ConT dist_nm) [th_tp]
  | dist_nm == ''Dist
  = do tp <- ingestType th_tp
       return $ DistType tp

-- Ingest types of the form @DistVar a -> Model c a@
ingestTypeApp TH.ArrowT [(matchTHTypeApp ->
                          (TH.ConT distvar_nm, [th_tp])),
                         (matchTHTypeApp ->
                          (TH.ConT model_nm,
                           [TH.VarT model_var, th_tp']))]
  | model_nm == ''Model && distvar_nm == ''DistVar && th_tp == th_tp'
  = do setTHVarRole model_var RoleDistSet
       tp <- ingestType th_tp
       return $ DistType tp

-- Throw an error for other types of the form @... -> Model c b@
ingestTypeApp TH.ArrowT args@(last ->
                              (matchTHTypeApp ->
                               (TH.ConT model_nm,
                                [TH.VarT _model_var, _th_tp'])))
  | model_nm == ''Model
  = throwError $ IngErrorBadDist (applyTHType TH.ArrowT args)


-- Ingest arrow types
ingestTypeApp TH.ArrowT [th_tp1, th_tp2] =
  do tp1 <- ingestType th_tp1
     tp2 <- ingestType th_tp2
     return $ ArrowType tp1 tp2

-- Ingest Grappa tuple types, which are of the form @ADT (TupleF ts) Id@
ingestTypeApp (TH.ConT adt_ctor) [(matchTHTypeApp ->
                                   (TH.ConT adt_nm,
                                    [(matchTHTypeList -> Just tps_th)]))]
  | adt_ctor == ''ADT && adt_nm == ''TupleF
  = do tps <- mapM ingestType tps_th
       return $ TupleType tps

-- Ingest Haskell list types as base types
ingestTypeApp TH.ListT [elem_tp_th] =
  do elem_tp <- ingestType elem_tp_th
     return $ mkHaskellListType elem_tp

-- Ingest Haskell tuple types as base types
ingestTypeApp (TH.TupleT n) tps_th
  | length tps_th == n
  = do tps <- mapM ingestType tps_th
       return $ mkHaskellTupleType tps

-- Match types of the form @ADT (T a1 ... an) Id@
ingestTypeApp (TH.ConT adt_ctor) [(matchTHTypeApp ->
                                   (TH.ConT adt_nm, adt_args))]
  | adt_ctor == ''ADT
  = do info <- ingestADTName adt_nm
       tps <- mapM ingestType adt_args
       return $ ADTType info tps

-- Match types of the form @Support a@
ingestTypeApp (TH.ConT support_nm) [arg]
  | support_nm == ''Support
  = do insts <- lift $ lift $ TH.reifyInstances ''Support [arg]
       (lhs, rhs) <-
         case insts of
           [TH.TySynInstD _ (TH.TySynEqn [lhs] rhs)] -> return (lhs, rhs)
           _ -> throwError $ IngErrorUnknownSupport arg
       th_subst <-
         case matchTHType lhs arg of
           Just th_subst -> return th_subst
           Nothing -> throwError $ IngErrorUnknownSupport arg
       ingestType $ substTHType th_subst rhs

-- Match other types of the form @T a1 ... an@
ingestTypeApp (TH.ConT nm) args =
  thReify nm >>= \th_info ->
  case th_info of
    TH.TyConI (TH.TySynD _ tyvars real_tp) -> do
      -- If nm is a type synonym, substitute into it and ingest again
      ingestType $
        substTHType (Map.fromList $ zip (map thTyVarName tyvars) args) real_tp
    _ ->
      do (tn, _) <- ingestBaseTypeName nm
         tps <- mapM ingestType args
         return $ BaseType tn tps

-- Match type variables with no arguments
ingestTypeApp (TH.VarT nm) [] =
  do tvar <- getTHVarTVar nm
     return $ VarType tvar

-- Error case
ingestTypeApp tp args = do
  throwError $ IngErrorMalformedType $ applyTHType tp args

-- | Ingest a TH type
ingestType :: TH.Type -> Ingest Type
ingestType tp =
  addIngestErrorContext (IngestCtxType tp) $
  uncurry ingestTypeApp $ matchTHTypeApp tp

-- | This should be simpler, because these types should be a lot more
-- abstract than they used to be. This also takes the
-- previously-ingested type and ensures that it corresponds.
ingestTypeAppInterp :: TH.Type -> [TH.Type] -> Ingest Type
ingestTypeAppInterp (TH.ConT dist_nm) [th_tp]
  | dist_nm == ''Dist = do
      tp <- ingestTypeInterp th_tp
      return $ DistType tp
ingestTypeAppInterp TH.ArrowT [th_tp1, th_tp2] = do
  tp1 <- ingestTypeInterp th_tp1
  tp2 <- ingestTypeInterp th_tp2
  return $ ArrowType tp1 tp2

ingestTypeAppInterp (TH.ConT adt_ctor) [(matchTHTypeApp ->
                                   (TH.ConT adt_nm,
                                    [(matchTHTypeList -> Just tps_th)]))]
  | adt_ctor == ''ADT && adt_nm == ''TupleF
  = do tps <- mapM ingestTypeInterp tps_th
       return $ TupleType tps

ingestTypeAppInterp
  (TH.ConT adt_ctor)
  [ (matchTHTypeApp -> (TH.ConT adt_nm, adt_args))
  ] | adt_ctor == ''ADT
  = do info <- ingestADTName adt_nm
       tps <- mapM ingestTypeInterp adt_args
       return $ ADTType info tps

ingestTypeAppInterp (TH.ConT nm) args
  | nm == ''GExpr =
    let [_, tp] = args in ingestTypeInterp tp
  | otherwise =
  thReify nm >>= \th_info ->
  case th_info of
    TH.TyConI (TH.TySynD _ tyvars real_tp) ->
      -- If nm is a type synonym, substitute into it and ingest again
      ingestTypeInterp $
        substTHType (Map.fromList $ zip (map thTyVarName tyvars) args) real_tp
    _ ->
      -- XXX be smarter about this case!
      let handle _ = do
            info <- ingestADTName nm
            tps <- mapM ingestTypeInterp args
            return $ ADTType info tps
      in flip catchError handle $ do
        (tn, _) <- ingestBaseTypeName nm
        tps <- mapM ingestTypeInterp args
        return $ BaseType tn tps

ingestTypeAppInterp (TH.VarT nm) [] = do
  tvar <- getTHVarTVar nm
  return $ VarType tvar

ingestTypeAppInterp tp args =
  throwError $ IngErrorMalformedInterpType $ applyTHType tp args

ingestTypeInterp :: TH.Type -> Ingest Type
ingestTypeInterp tp =
  addIngestErrorContext (IngestCtxInterpType tp) $
  uncurry ingestTypeAppInterp $ matchTHTypeApp tp

-- | Ingest a TH type
ingestTopTypeInterp :: TH.Type -> Ingest Type
ingestTopTypeInterp t =
  addIngestErrorContext (IngestCtxType t) $
    case matchTHTypeApp t of
      (tp, [_repr, arg])
        | tp == TH.ConT ''GExpr ->
            uncurry ingestTypeAppInterp $ matchTHTypeApp arg
      _ ->
        throwError $ IngErrorNonGExpr t


--
-- * Ingest a TH Type as a Top-Level Grappa Type
--

-- | Ingest a TH constraint. This may return a Grappa 'ClassConstr', for normal
-- named constraints, or it may simply get internalized into the 'Ingest'
-- environment for TH constraints that represent membership in a dist set.
ingestConstraint :: TH.Type -> Ingest (Maybe ClassConstr)

-- For a constraint c tp where c is a TH type variable, assume that c represents
-- a distribution set, and add tp to the current distribution set
ingestConstraint (matchTHTypeApp -> (TH.VarT th_c, [th_tp])) =
  do setTHVarRole th_c RoleDistSet
     tp <- ingestType th_tp
     addToDistSet tp
     return Nothing

-- Any other constraint is treated as a named constraint
ingestConstraint (matchTHTypeApp -> (TH.ConT nm, [tp])) =
  (Just . NamedConstr (ConstrInfo { constr_th_name = nm })) <$>
  ingestType tp

-- Anything that does not match one of the above cases is an error
ingestConstraint constr = throwError $ IngErrorMalformedConstr constr


-- | Ingest a list of constraints
ingestConstraints :: [TH.Type] -> Ingest [ClassConstr]
ingestConstraints tps = catMaybes <$> mapM ingestConstraint tps


-- | Ingest a TH constraint for the interpretation of a function
ingestConstraintInterp :: TH.Type ->
                          Ingest (Either InterpConstr (Maybe ClassConstr))

-- Match constraints of the form Interp__ADT repr (nm tp1 ... tpn)
ingestConstraintInterp (matchTHTypeApp ->
                        (TH.ConT nm, [TH.VarT repr_var, adt_tp]))
  | nm == ''Interp__ADT
  , (TH.ConT adt_nm_th, tps_th) <- matchTHTypeApp adt_tp
  = do setTHVarRole repr_var RoleReprVar
       adt_info <- ingestADTName adt_nm_th
       tps <- mapM ingestType tps_th
       return $ Left $ InterpADTConstr adt_info tps

-- Match constraints of the form Interp__XXX repr tp1 ... tpn
ingestConstraintInterp (matchTHTypeApp ->
                        (TH.ConT nm, (TH.VarT repr_var : tps_th)))
  | L.isPrefixOf "Interp__" (TH.nameBase nm)
  = do setTHVarRole repr_var RoleReprVar
       tps <- mapM ingestType tps_th
       return $ Left $ InterpConstr (ConstrInfo { constr_th_name = nm }) tps

-- Match constraints of the form ValidRepr repr and return a Nothing
ingestConstraintInterp (matchTHTypeApp ->
                        (TH.ConT validrepr_nm, [TH.VarT repr_var]))
  | validrepr_nm == ''ValidRepr
  = do setTHVarRole repr_var RoleReprVar
       return $ Right Nothing

-- Other constraints get interpreted as normal constraints
ingestConstraintInterp constr = Right <$> ingestConstraint constr


-- | Ingest a list of constraints for the interpretation of a function
ingestConstraintsInterp :: [TH.Type] -> Ingest ([InterpConstr], [ClassConstr])
ingestConstraintsInterp constrs_in =
  do (interp_constrs, maybe_constrs) <-
       partitionEithers <$> mapM ingestConstraintInterp constrs_in
     return (interp_constrs, catMaybes maybe_constrs)


-- | Old-style ingest of a top-type
oldIngestTopType :: TH.Type -> Ingest TopType
oldIngestTopType top_tp_th =
  withLocalIngestEnv $
  addIngestErrorContext (IngestCtxTopType top_tp_th) $
  do let (_, ctx, th_dom_tps, th_ran_tp) = matchTHTopType top_tp_th
     constrs <- ingestConstraints ctx
     dom_tps <- mapM ingestType th_dom_tps
     ran_tp <- ingestType th_ran_tp
     let tvars = Set.toList $ freeVars (dom_tps, ran_tp)
     dist_set <- ingest_dist_set <$> get
     return $ TopType tvars constrs [] dist_set dom_tps ran_tp


-- | Ingest the TH types for an operator and its interpretation as a Grappa
-- top-level type.
--
-- FIXME: currently, this just ingests the type of the interpretation, and
-- mostly ignores the type of the underlying operator, but it should do a
-- double-check that the types match and that the constraints for the
-- interpertation are a superset of those for the underlying operator.
ingestTopType :: TH.Type -> TH.Type -> Ingest TopType
ingestTopType old_top_tp_th interp_top_tp_th =
  withLocalIngestEnv $
  addIngestErrorContext (IngestCtxTopType interp_top_tp_th) $
  case matchTHTopInterpType interp_top_tp_th of
    Just (_, ctx, repr_var, th_dom_tps, th_ran_tp) -> do
      setTHVarRole repr_var RoleReprVar
      (interp_constrs, constrs1) <- ingestConstraintsInterp ctx
      dom_tps <- mapM ingestType th_dom_tps
      ran_tp <- ingestType th_ran_tp
      dist_set1 <- ingest_dist_set <$> get
      let tvars = Set.toList $ freeVars (dom_tps, ran_tp)
      -- NOTE: we need to ingest all the non-interp constraints, for two
      -- reasons: we need to get the dist-set; and for, e.g., the (+) operator,
      -- we will only get the Interp__'plus class, not its super-classes (such
      -- as the Num class). Both of these are only needed for the non-interp
      -- compilation. In order to ingest these old-style non-interp constraints,
      -- we ingest the old-style top type, syntactically match it against the
      -- new type, and use the resulting renaming to ingest its constraints
      TopType _ old_constrs _ old_dist_set old_dom_tps old_ran_tp <-
        oldIngestTopType old_top_tp_th
      let old_body = mkArrowType old_dom_tps old_ran_tp
          interp_body = mkArrowType dom_tps ran_tp
      ren <-
        case synMatch old_body interp_body of
          Nothing -> throwError $ IngErrorDifferentTypes old_body interp_body
          Just ren -> return ren
      let constrs2 = rename ren old_constrs
      let dist_set2 = Set.map (rename ren) old_dist_set
      let constrs = L.nub (constrs1 ++ constrs2)
      let dist_set = Set.union dist_set1 dist_set2
      return $ TopType tvars constrs interp_constrs dist_set dom_tps ran_tp
    Nothing ->
      throwError $ IngErrorMalformedTopInterpType interp_top_tp_th
