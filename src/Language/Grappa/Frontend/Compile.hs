{-# LANGUAGE DataKinds, TypeFamilies, EmptyDataDecls, GADTs, TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE ParallelListComp, ViewPatterns #-}

module Language.Grappa.Frontend.Compile where

import System.IO
import qualified Data.Text as T
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH

import qualified Data.Foldable as F

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified System.Exit as Sys

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

import AlexTools (startPos)

import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.Parser (parseDecls, parseGPrior, Parse, ParseError)
import Language.Grappa.Frontend.IngestEmitType
import Language.Grappa.Frontend.Resolve
import Language.Grappa.Frontend.FixupOps
import Language.Grappa.Frontend.Matching
import Language.Grappa.Frontend.TypeCheck
import Language.Grappa.Frontend.DataSource
import Language.Grappa.Frontend.Errors()
import Language.Grappa.Inference
import Language.Grappa.Interp
import Language.Grappa.GrappaInternals

--
-- Monad for the Whole Grappa Compiler
--

data CompileContext = CompileCtxExp (Exp Rewritten)
                    | CompileCtxVExp (VExp Rewritten)
                    | CompileCtxPrExp (SourceExp Rewritten)
                    | CompileGenExp (GenExp Rewritten)
                    | CompileListCompArm (ListCompArm Rewritten)
                    | CompileCtxStmt (Stmt Rewritten)
                    | CompileCtxGPStmt (GPriorStmt Rewritten)
                    | CompileCtxPattern (CompiledPattern Rewritten)
                    | CompileCtxDecl (Decl Rewritten)
                    | CompileCtxType Type
                    | CompileCtxTopType TopType
                    deriving Show

instance PP.Pretty CompileContext where
  pretty (CompileCtxExp ee) =
    PP.text "expression" PP.<$$> PP.pretty ee
  pretty (CompileCtxVExp ve) =
    PP.text "v-expression" PP.<$$> PP.pretty ve
  pretty (CompileCtxPrExp se) =
    PP.text "source expression" PP.<$$> PP.pretty se
  pretty (CompileCtxStmt stmt) =
    PP.text "statement" PP.<$$> PP.pretty stmt
  pretty (CompileCtxGPStmt stmt) =
    PP.text "gprior statement" PP.<$$> PP.pretty stmt
  pretty (CompileCtxPattern pat) =
    PP.text "pattern" PP.<$$> PP.pretty pat
  pretty (CompileCtxDecl decl) =
    PP.text "declaration" PP.<$$> PP.pretty decl
  pretty (CompileCtxType typ) =
    PP.text "type" PP.<$$> PP.pretty typ
  pretty (CompileCtxTopType tt) =
    PP.text "top type" PP.<$$> PP.pretty tt
  pretty (CompileListCompArm tt) =
    PP.text "list comprehension arm" PP.<$$> PP.pretty tt
  pretty (CompileGenExp tt) =
    PP.text "generator expression" PP.<$$> PP.pretty tt

-- | The type of objects that we can add to the compilation error context
class HasCompileContext a where
  mkCompileContext :: a -> CompileContext

instance HasCompileContext Type where
  mkCompileContext = CompileCtxType
instance HasCompileContext TopType where
  mkCompileContext = CompileCtxTopType
instance HasCompileContext (Exp Rewritten) where
  mkCompileContext = CompileCtxExp
instance HasCompileContext (VExp Rewritten) where
  mkCompileContext = CompileCtxVExp
instance HasCompileContext (SourceExp Rewritten) where
  mkCompileContext = CompileCtxPrExp
instance HasCompileContext (GenExp Rewritten) where
  mkCompileContext = CompileGenExp
instance HasCompileContext (ListCompArm Rewritten) where
  mkCompileContext = CompileListCompArm
instance HasCompileContext (Stmt Rewritten) where
  mkCompileContext = CompileCtxStmt
instance HasCompileContext (GPriorStmt Rewritten) where
  mkCompileContext = CompileCtxGPStmt
instance HasCompileContext (CompiledPattern Rewritten) where
  mkCompileContext = CompileCtxPattern
instance HasCompileContext (Decl Rewritten) where
  mkCompileContext = CompileCtxDecl

-- | The Grappa compilation errors
data GrappaError = GErrorParse ParseError
                 | GErrorResolve ResolveError
                 | GErrorEmit EmitError
                 | GErrorTypeCheck TypeError
                 | GErrorMisc String
                 | GErrorMatching PatternMatchError
                 | GErrorContext GrappaError CompileContext
                 deriving Show

instance PP.Pretty GrappaError where
  pretty (GErrorParse err) =
    PP.text "Parse error:" PP.<$$> PP.nest 2 (PP.pretty err)
  pretty (GErrorResolve err) =
    PP.text "Resolution error:" PP.<$$> PP.nest 2 (PP.pretty err)
  pretty (GErrorEmit err) =
    PP.text "Emit error:" PP.<$$> PP.nest 2 (PP.pretty err)
  pretty (GErrorTypeCheck err) =
    PP.text "Type error:" PP.<$$> PP.nest 2 (PP.pretty err)
  pretty (GErrorMisc err) =
    PP.text "Compilation error:" PP.<+> PP.text err
  pretty (GErrorMatching err) =
    -- FIXME: implement pretty-printing for matching errors
    PP.text "Pattern-matching error:" PP.<+> PP.text (show err)
  pretty (GErrorContext err ctx) =
    PP.pretty err PP.<$$>
    PP.text "In compiling" PP.<$$> PP.nest 2 (PP.pretty ctx)

-- | The type of environments for compilation to TH
data CompileEnv =
  CompileEnv { compile_emit_env :: EmitEnv,
               compile_res_env :: ResolveEnv,
               compile_current_function :: Maybe Ident,
               compile_fix_parameter :: Maybe TH.Name,
               compile_model_subcase_vpatt :: Maybe (CompiledPattern Rewritten),
               compile_debug_handle :: Maybe Handle }

-- | Build an empty 'CompileEnv', given a TH name for the @c@ variable and an
-- optional 'Handle' for debugging output
emptyCompileEnv :: Maybe Handle -> TH.Name -> CompileEnv
emptyCompileEnv debugH repr =
  CompileEnv { compile_emit_env = emptyEmitEnv repr,
               compile_res_env = emptyResolveEnv,
               compile_current_function = Nothing,
               compile_fix_parameter = Nothing,
               compile_model_subcase_vpatt = Nothing,
               compile_debug_handle = debugH }

-- | The monad for compiling to TH
type Compile = StateT CompileEnv (ExceptT GrappaError TH.Q)

instance TCDebuggable Compile where
  tcDebug str =
    do debugH <- compile_debug_handle <$> get
       case debugH of
         Just h ->
           lift $ lift $ TH.runIO
           (hPutStrLn h (showString "Debug: " str) >> hFlush h)
         Nothing -> return ()

-- | Run a 'Compile' computation in an extended error context
withCompileCtx :: HasCompileContext a => a -> Compile b -> Compile b
withCompileCtx ctx_obj m =
  let ctx = mkCompileContext ctx_obj in
  tcDebug ("Compiler context: " ++ show ctx) >>
  catchError m (\e -> throwError (GErrorContext e ctx))

-- | Get the top-level V-pattern used by the current model case
getModelSubCasePattern :: Compile (CompiledPattern Rewritten)
getModelSubCasePattern =
  do maybe_patt <- compile_model_subcase_vpatt <$> get
     case maybe_patt of
       Just patt -> do
         return patt
       Nothing -> error "getModelSubCasePattern: missing model case pattern!"

-- | Run a 'Compile' computation using a given model case pattern
withModelSubCasePattern :: Pattern Rewritten -> Compile a -> Compile a
withModelSubCasePattern patt m =
  do saved_env <- get
     put $ saved_env { compile_model_subcase_vpatt = Just patt }
     ret <- m
     modify $ \env -> env { compile_model_subcase_vpatt =
                              compile_model_subcase_vpatt saved_env }
     return ret

-- | Run a compilation computation in a local compilation environment, saving
-- only the resolution environment
withLocalCompileEnv :: Compile a -> Compile a
withLocalCompileEnv m =
  do saved_env <- get
     res <- m
     modify $ \env ->
       env { compile_emit_env = compile_emit_env saved_env,
             compile_model_subcase_vpatt = compile_model_subcase_vpatt saved_env }
     return res

withCurrentFunction :: Ident -> Compile a -> Compile a
withCurrentFunction nm m = do
  saved_env <- get
  fix_th <- embedM $ TH.newName "fix"
  put $ saved_env { compile_current_function = Just nm
                  , compile_fix_parameter = Just fix_th
                  }
  res <- m
  modify $ \env -> env { compile_current_function = Nothing
                       , compile_fix_parameter = Nothing
                       }
  return res

-- | Add a resolved global name to the name resolution environment
addResolvedGName :: Ident -> ResGName -> Compile ()
addResolvedGName nm gname =
  modify $ \env -> env { compile_res_env =
                           resolveEnvAddGname nm gname $ compile_res_env env }

instance SubMonad TH.Q Compile where
  embedM m = lift $ lift m

instance SubMonad Parse Compile where
  embedM (Right a) = return a
  embedM (Left err) = throwError $ GErrorParse err

instance SubMonad Resolve Compile where
  embedM m =
    do res_env <- compile_res_env <$> get
       (res, res_env') <-
         lift $ withExceptT GErrorResolve $ runStateT m res_env
       modify $ \env -> env { compile_res_env = res_env' }
       return res

instance SubMonad Emit Compile where
  embedM m =
    do emit_env <- compile_emit_env <$> get
       (res, emit_env') <- lift $ withExceptT GErrorEmit $ runStateT m emit_env
       modify $ \env -> env { compile_emit_env = emit_env' }
       return res

instance SubMonad TypeCheck Compile where
  embedM m =
    do debugH <- compile_debug_handle <$> get
       lift $ withExceptT GErrorTypeCheck $ ExceptT $ runTypeCheck debugH m

instance SubMonad MatchM Compile where
  embedM m =
    fmap fst $ lift $ withExceptT GErrorMatching $ runStateT m emptyMatchEnv

-- | Run a 'Compile' computation in the 'TH.Q' monad
runCompile :: Compile a -> TH.Q a
runCompile m =
  do repr_var <- TH.newName "repr"
     -- FIXME: figure out how to catch IO exceptions and close debugH on error
     debugH <- TH.runIO (openFile "./grappa-compile-log" WriteMode)
     eith <- runExceptT $ runStateT m (emptyCompileEnv (Just debugH) repr_var)
     TH.runIO $ hClose debugH
     case eith of
       Right (a,_) -> return a
       Left err -> TH.runIO $ do
         PP.putDoc (PP.pretty err)
         Sys.exitFailure


--
-- * Helper Functions for Building Template Haskell
--

-- | Apply a TH expression to a list of arguments
applyTHExp :: TH.Exp -> [TH.Exp] -> TH.Exp
applyTHExp = foldl TH.AppE

-- | Apply a TH expression to a list of arguments
applyTHExpInterp :: TH.Exp -> [TH.Exp] -> TH.Exp
applyTHExpInterp = foldl go
  where go x xs = TH.AppE (TH.AppE (TH.VarE 'interp__'app) x) xs

-- | Build a TH expression of type @'Id' a@ from one of type @a@
mkIdTHExp :: TH.Exp -> TH.Exp
mkIdTHExp expr = applyTHExp (TH.ConE 'Id) [expr]

-- | Build a TH pattern of type @'Id' a@ from one of type @a@
mkIdTHPat :: TH.Pat -> TH.Pat
mkIdTHPat patt = TH.ConP 'Id [patt]

-- | Build a TH expression of type @'ADT' adt 'Id'@ for a Grappa constructor of
-- @adt@ and its argument expressions
mkADTCtorTHExp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkADTCtorTHExp ctor args_th =
  if ctor_is_adt ctor then
    applyTHExp (TH.ConE 'ADT) [applyTHExp (TH.ConE $ ctor_th_name ctor) $
                               map mkIdTHExp args_th]
  else
    error "mkADTCtorTHExp: non-ADT constructor"

-- | Build a TH expression of type @'DistVar ('ADT' adt 'Id')@ for a Grappa
-- constructor of @adt@ and its argument expressions
mkCtorDistVarTHExp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkCtorDistVarTHExp ctor args_th =
  if ctor_is_adt ctor then
    applyTHExp (TH.ConE 'VADT) [applyTHExp (TH.ConE $ ctor_th_name ctor) args_th]
  else
    error "mkCtorDistVarTHExp: non-ADT constructor"


-- | Build a TH expression for a constructor that is partially applied to its
-- arguments, using the partially-applied lambda expression
--
-- > \x1 ... xn -> ADT (C (Id arg1) ... (Id argm) (Id x1) .. (Id xn))
--
-- for ADT constructor @C@
mkCtorLamTHExp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkCtorLamTHExp ctor args_th =
  if ctor_is_adt ctor then
    let vars_th =
          map (\i -> TH.mkName $ "x" ++ show i)
          [1 .. (ctorArity ctor - length args_th)]
        ctor_args_th = args_th ++ map TH.VarE vars_th in
    (if length vars_th > 0 then TH.LamE (map TH.VarP vars_th) else id) $
    mkADTCtorTHExp ctor ctor_args_th
  else
    applyTHExp (TH.ConE $ ctor_th_name ctor) args_th


mkLamInterp :: [TH.Pat] -> TH.Exp -> TH.Exp
mkLamInterp pats body = F.foldr go body pats
  where go p e =
          applyTHExp (TH.VarE 'interp__'lam) [ TH.LamE [p] e ]

mkCtorLamTHExpInterp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkCtorLamTHExpInterp ctor args_th =
  if ctor_is_adt ctor then
    let vars_th =
          map (\i -> TH.mkName $ "x" ++ show i)
          [1 .. (ctorArity ctor - length args_th)]
        ctor_args_th = args_th ++ map TH.VarE vars_th in
    mkLamInterp (map TH.VarP vars_th)
      (applyTHExp (TH.VarE 'interp__'injADT)
        [applyTHExp (TH.ConE (ctor_th_name ctor)) ctor_args_th])
  else
    applyTHExp (TH.ConE $ ctor_th_name ctor) args_th

-- | Build a TH pattern of type @'ADT' adt 'Id'@ for a Grappa constructor of
-- @adt@ and its argument patterns
mkCtorTHPat :: CtorInfo -> [TH.Pat] -> TH.Pat
mkCtorTHPat ctor patts_th =
  if ctor_is_adt ctor then
    TH.ConP 'ADT [TH.ConP (ctor_th_name ctor) $
                  map (\p -> TH.ConP 'Id [p]) patts_th]
  else
    TH.ConP (ctor_th_name ctor) patts_th

-- | Build a TH expression of type @'TupleF' ts f ('ADT' ('TupleF' ts) 'Id')@
-- from arguments of type @f t1@, @f t2@, etc., for the types @ti@ in the list
-- @ts@ of types. This is called the "body" of a tuple because, when @f@ is
-- 'Id', it is the argument to the 'ADT' constructor needed to make an actual
-- Grappa tuple of type @'ADT' ('TupleF' ts) 'Id'@.
mkTupleBodyTHExp :: [TH.Exp] -> TH.Exp
mkTupleBodyTHExp [] = TH.ConE 'Tuple0
mkTupleBodyTHExp args@[_] = applyTHExp (TH.ConE 'Tuple1) args
mkTupleBodyTHExp args@[_,_] = applyTHExp (TH.ConE 'Tuple2) args
mkTupleBodyTHExp args@[_,_,_] = applyTHExp (TH.ConE 'Tuple3) args
mkTupleBodyTHExp args@[_,_,_,_] = applyTHExp (TH.ConE 'Tuple4) args
mkTupleBodyTHExp (a:b:c:d:e:rest) =
  applyTHExp (TH.ConE 'TupleN) [a,b,c,d,e,mkTupleBodyTHExp rest]

-- | Build a TH expression for a Grappa tuple of type @'ADT' ('TupleF' ts) 'Id'@
-- from TH expressions with types @t1@, @t2@, etc., which are the types in the
-- @ts@ list
mkTupleTHExp :: [TH.Exp] -> TH.Exp
mkTupleTHExp exps =
  applyTHExp (TH.ConE 'ADT) [mkTupleBodyTHExp $ map mkIdTHExp exps]

-- | Build a TH expression for a Grappa tuple inside a 'DistVar'
mkTupleDistVarTHExp :: [TH.Exp] -> TH.Exp
mkTupleDistVarTHExp exps =
  applyTHExp (TH.ConE 'VADT) [mkTupleBodyTHExp exps]

-- | Build a TH pattern for the "body" of a Grappa tuple (see 'mkTupleBodyTHExp'
-- for more description of what this means)
mkTupleBodyTHPat :: [TH.Pat] -> TH.Pat
mkTupleBodyTHPat [] = TH.ConP 'Tuple0 []
mkTupleBodyTHPat patts@[_] = TH.ConP 'Tuple1 patts
mkTupleBodyTHPat patts@[_,_] = TH.ConP 'Tuple2 patts
mkTupleBodyTHPat patts@[_,_,_] = TH.ConP 'Tuple3 patts
mkTupleBodyTHPat patts@[_,_,_,_] = TH.ConP 'Tuple4 patts
mkTupleBodyTHPat (a:b:c:d:e:rest) =
  TH.ConP 'TupleN [a,b,c,d,e,mkTupleBodyTHPat rest]

-- | Build a TH pattern for a Grappa tuple
mkTupleTHPat :: [TH.Pat] -> TH.Pat
mkTupleTHPat patts = TH.ConP 'ADT [mkTupleBodyTHPat $ map mkIdTHPat patts]

-- | Build a TH expression for the 'sourceFormat' field of a 'SourceFile'
mkFormatTHExp :: String -> Compile TH.Exp
mkFormatTHExp "csv" = return (TH.ConE 'CSV)
mkFormatTHExp "json" = return (TH.ConE 'JSON)
mkFormatTHExp str =
  throwError (GErrorMisc ("Unknown input format '" ++ str ++ "'"))

--
-- * Compiling Grappa to TH
--

-- | Typeclass for things that can be compiled to TH
class Compilable a th | a -> th where
  compile :: a -> Compile th

instance Compilable a th => Compilable [a] [th] where
  compile = mapM compile

instance Compilable Type TH.Type where
  compile tp = withCompileCtx tp $ embedM $ emitType tp

instance Compilable TopType TH.Type where
  compile top_tp = withCompileCtx top_tp $ embedM $ emitTopType top_tp

instance Compilable (Name Rewritten) TH.Exp where
  compile (LocalName x) = do
    -- If this isn't set, then we're doing something wrong
    Just curr <- compile_current_function <$> get
    Just self <- compile_fix_parameter <$> get
    return $ TH.VarE $ if curr == x then self else TH.mkName (T.unpack x)
  compile (GlobalName nm) = return $ TH.VarE $ gname_th_name nm
  compile (CtorName ctor) =
    return $ mkCtorLamTHExpInterp ctor []

instance Compilable (Exp Rewritten) TH.Exp where
  compile expr = withCompileCtx expr $ go expr where
    go (NameExp nm _tp) = compile nm
    go (LiteralExp (IntegerLit i) _) = do
      let exp_th = TH.AppE (TH.VarE 'interp__'integer)
                           (TH.LitE (TH.IntegerL i))
      return $ exp_th
    go (LiteralExp (RationalLit r) _) = do
      let exp_th = TH.AppE (TH.VarE 'interp__'rational)
                           (TH.LitE (TH.RationalL r))
      return $ exp_th
    go (SigExp e _) = do
      compile e
    go (AppExp f args _) = do
      f_th <- compile f
      args_th <- compile args
      let goI x rs = (TH.VarE 'interp__'app) `TH.AppE` x `TH.AppE` rs
      return $ foldl goI f_th args_th
    go (TupleExp es _) = do
      es_th <- compile es
      let tup_th = mkTupleBodyTHExp es_th
      return $ TH.AppE (TH.VarE 'interp__'injTuple) tup_th
    go (LetExp n _ lhs rhs _) = do
      lhs_th <- compile lhs
      rhs_th <- compile rhs
      return $ TH.LetE [TH.ValD (TH.VarP $ TH.mkName $ T.unpack n)
                        (TH.NormalB lhs_th) []] rhs_th
    go (CaseExp scrut cases _) =
      compileInterpCase scrut cases
    go (ModelExp cases _) = do
      compileSubCases cases
    go (IfExp c t e _) = do
      c_th <- compile c
      t_th <- compile t
      e_th <- compile e
      return $ applyTHExp (TH.VarE 'interp__'ifThenElse) [c_th, t_th, e_th]
    go (FunExp (FunCase pats body) _) = do
      let pats_th = map compileVarPat pats
      body_th <- compile body
      return $ mkLamInterp pats_th body_th
    go (ListExp enabled _) = notEnabled enabled
    go (ParensExp enabled _) = notEnabled enabled
    go (OpExp enabled _ _ _) = notEnabled enabled


--
-- ** Pattern-Matching Compilation
--

class (Compilable body TH.Exp) => CaseType r body | r -> body where
  getPattern :: r -> Pattern Rewritten
  getBody    :: r -> body
  getTupleProjector :: r -> TH.Name

instance CaseType (ExpCase Rewritten) (Exp Rewritten) where
  getPattern (ExpCase pat _ _ _) = pat
  getBody (ExpCase _ body _ _) = body
  getTupleProjector _ = 'interp__'projTuple

instance CaseType (StmtCase Rewritten) (Stmt Rewritten) where
  getPattern (StmtCase pat _ _) = pat
  getBody (StmtCase _ body _) = body
  getTupleProjector _ = 'interp__'projTupleStmt

instance CaseType (ModelSubCase Rewritten) (Stmt Rewritten) where
  getPattern (ModelSubCase pat _ _) = pat
  getBody (ModelSubCase _ _ body) = body
  getTupleProjector _ = 'interp__'projTupleStmt

compileInterpCase :: (Show r, CaseType r b) => Exp Rewritten -> [r] -> Compile TH.Exp
compileInterpCase scrut cases
  | any isCtor cases = do
      scrut_th <- compile scrut
      cases_th <- forM cases $ \ cs -> do
        patt_th <- compile (getPattern cs)
        body_th <- compile (getBody cs)
        return $ TH.Match patt_th (TH.NormalB body_th) []
      scr_var <- embedM $ TH.newName "scrut"
      return $ applyTHExp (TH.VarE 'interp__'projADT)
        [ scrut_th
        , TH.LamE [TH.VarP scr_var] $
            TH.CaseE (TH.VarE scr_var) cases_th
        ]
  | any isLit cases = do
      scrut_th <- compile scrut
      compileLitMatch scrut_th cases
  | [cs] <- cases
  , CompiledTuplePat pats _ <- getPattern cs = do
      scrut_th <- compile scrut
      let pat_th = map compileVarPat pats
      body_th <- compile (getBody cs)
      return $ applyTHExp (TH.VarE (getTupleProjector cs))
        [ scrut_th
        , TH.LamE [mkTupleBodyTHPat pat_th] body_th
        ]
  | [] <- cases = error "Unexpected empty case alternatives list"
  | otherwise = error ("Unsure how to deal with these pattern matches: " ++ show cases)
  where isCtor (getPattern->CompiledCtorPat {}) = True
        isCtor _ = False
        isLit (getPattern->CompiledLitPat {}) = True
        isLit _ = False

compileLitMatch :: (Show r, CaseType r b) => TH.Exp -> [r] -> Compile TH.Exp
compileLitMatch _ [cs] | CompiledBasicPattern _ <- getPattern cs =
  compile (getBody cs)
compileLitMatch scrut (cs:rs) | CompiledLitPat l tp <- getPattern cs = do
  l_th <- compile (LiteralExp l tp :: Exp Rewritten)
  c_th <- compile (getBody cs)
  e_th <- compileLitMatch scrut rs
  let cmp = TH.VarE $ case l of
        IntegerLit _  -> 'interp__'eqInteger
        RationalLit _ -> 'interp__'eqRational
  let cond_th = applyTHExp cmp [scrut, l_th]
  return $ applyTHExp (TH.VarE 'interp__'ifThenElse) [cond_th, c_th, e_th]
compileLitMatch _ (cs:_) =
  error ("Unexpected pattern in compiling literal matches: " ++ show (getPattern cs))
compileLitMatch _ [] =
  error "Unexpected empty cases in compiling literal matches"


--
-- ** Compiling Posterior Expressions
--

compileFileSource :: Filename -> T.Text -> Type -> Compile TH.Exp
compileFileSource filename fmt tp = do
  let ctor = case matchListType tp of
        Just (TupleType _) ->
          -- File reads of tuple type, i.e., of type @[(t1, ..., tn)]@,
          -- become a SourceReadFileRow
          'SourceReadFileRow
        Just _ ->
          -- File reads of non-tuple type become a SourceReadFileField
          'SourceReadFileField
        Nothing ->
          error "File read at non-list type!"
  let file_th = case filename of
        FileStringLit lt -> TH.litE (TH.StringL (T.unpack lt))
        FileVarName   nm -> TH.varE (TH.mkName (T.unpack nm))
  tp_th <- compile tp
  fmt_th <- mkFormatTHExp (T.unpack fmt)
  embedM [|
        ($(TH.conE ctor)
         (SourceFile
          $(file_th)
          $(return fmt_th)))
        :: Source $(return tp_th)
        |]

compileBasicDistVarPatt :: CompiledVarPattern Rewritten -> Compile TH.Pat
compileBasicDistVarPatt (VarCPat x tp) = do
  tp_th <- compile tp
  let dv_tp = TH.AppT (TH.ConT ''DistVar) tp_th
  return $ TH.SigP (TH.VarP $ TH.mkName $ T.unpack x) (dv_tp)
compileBasicDistVarPatt (WildCPat _) = embedM [p| _ |]

-- | Compile a Grappa pattern into a TH pattern over 'DistVar's
compileDistVarPatt :: Pattern Rewritten -> Compile TH.Pat
compileDistVarPatt (CompiledBasicPattern pat) =
  compileBasicDistVarPatt pat
compileDistVarPatt (CompiledCtorPat ctor patts _) =
  do patts_th <- mapM compileBasicDistVarPatt patts
     param_args_th <- forM patts_th $ \_ -> embedM [| VParam |]
     embedM [p| (matchADTDistVar
                 $(return $
                   applyTHExp (TH.ConE $ ctor_th_name ctor) param_args_th) ->
                 ($(return $ TH.ConP (ctor_th_name ctor) patts_th))) |]
compileDistVarPatt (CompiledTuplePat patts _) =
  do patts_th <- mapM compileBasicDistVarPatt patts
     param_args_th <- forM patts_th $ \_ -> embedM [| VParam |]
     embedM [p| (matchADTDistVar
                 $(return $ mkTupleBodyTHExp param_args_th) ->
                 ($(return $ mkTupleBodyTHPat patts_th))) |]
compileDistVarPatt (CompiledLitPat _ (ADTType _ _)) =
  error "compileDistVarPatt: literal pattern of ADT type!"
compileDistVarPatt (CompiledLitPat (IntegerLit i) _) =
  embedM $ [p| (matchAtomicDistVar $(TH.litE $ TH.IntegerL i) -> True) |]
compileDistVarPatt (CompiledLitPat (RationalLit r) _) =
  embedM $ [p| (matchAtomicDistVar $(TH.litE $ TH.RationalL r) -> True) |]

compileArmExpr :: ListCompArm Rewritten -> Compile TH.Exp
compileArmExpr lca@(ListCompArm _ ge) = withCompileCtx lca $ compile ge

compileArmPat :: [ListCompArm Rewritten] -> Compile TH.Pat
compileArmPat [ListCompArm pat _] = compileDistVarPatt pat
compileArmPat _ = error "FIXME"
  -- do
  --   let pats = [ (pat, case pat of
  --                    _ -> getTypeOf pat)
  --              | ListCompArm pat _ <- lcs ]
  --   compileDistVarPatt (CompiledTuplePat (map fst pats) (TupleType (map snd pats)))

zipTypes :: Type -> Type -> Compile Type
zipTypes t1 t2
  | Just e1 <- matchListType t1
  , Just e2 <- matchListType t2
  = return (mkListType (TupleType [e1, e2]))
zipTypes _ _ = error "Trying to zip a non-list!"

instance Compilable (GenExp Rewritten) TH.Exp where
  compile ge = withCompileCtx ge $ compile' ge where
    compile' (VarGenExp nm tp) = do
      let nm_th = (TH.AppE (TH.VarE 'allowUnused) (TH.VarE nm))
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE nm_th tp_th)
    compile' (BoundVarGenExp nm tp) =
      let nm' = TH.mkName $ T.unpack nm
      in TH.SigE (TH.AppE (TH.VarE 'allowUnused) (TH.VarE nm')) <$>
         TH.AppT (TH.ConT ''Source) <$> compile tp
    compile' (FileGenExp filename fmt tp) =
      compileFileSource filename fmt tp
    compile' (RangeGenExp bg (Just to) st tp) = do
      let Just elm = matchListType tp
      elem_th <- compile elm
      let bgE = return (TH.SigE (TH.LitE (TH.IntegerL bg)) elem_th)
          stE = return (TH.LitE (TH.IntegerL st))
          toE = return (TH.LitE (TH.IntegerL to))
      ee_th <-  lift $ lift [| dvToSource (embedDistVar (enumFromToByF $(bgE) $(toE) $(stE))) |]
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE ee_th tp_th)
    compile' (RangeGenExp bg Nothing st tp) = do
      let Just elm = matchListType tp
      elem_th <- compile elm
      let bgE = return (TH.SigE (TH.LitE (TH.IntegerL bg)) elem_th)
          stE = return (TH.LitE (TH.IntegerL st))
      ee_th <- lift $ lift [| dvToSource (embedDistVar (enumFromByF $(bgE) $(stE))) |]
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE ee_th tp_th)

instance Compilable (SourceExp Rewritten) TH.Exp where
  compile sexp = withCompileCtx sexp $ compile' sexp where
    compile' :: SourceExp Rewritten -> Compile TH.Exp
    compile' (VarSrcExp nm tp) = do
      -- A variable in a source expression literally refers to a Haskell
      -- variable, which could either be a concrete value or it could itself be
      -- a Source object, so we use the toSource method to convert it to Source,
      -- which effectively uses GHC to do this case distinction
      let ee_th = applyTHExp (TH.VarE 'toSource) [TH.VarE nm]
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE ee_th tp_th)
    compile' (BoundVarSrcExp nm tp) =
      -- This is always going to be a variable bound somewhere in the source
      -- expression
      let nm' = TH.mkName $ T.unpack nm
      in TH.SigE (applyTHExp (TH.VarE 'toSource) [TH.VarE nm']) <$>
         TH.AppT (TH.ConT ''Source) <$> compile tp
    compile' (WildSrcExp tp) =
      TH.SigE (TH.ConE 'SourceParam) <$>
      TH.AppT (TH.ConT ''Source) <$> compile tp
    compile' (LiteralSrcExp (IntegerLit i) tp) =
      TH.SigE (applyTHExp (TH.ConE 'SourceData) [TH.LitE $ TH.IntegerL i]) <$>
      TH.AppT (TH.ConT ''Source) <$> compile tp
    compile' (LiteralSrcExp (RationalLit r) tp) =
      TH.SigE (applyTHExp (TH.ConE 'SourceData) [TH.LitE $ TH.RationalL r]) <$>
      TH.AppT (TH.ConT ''Source) <$> compile tp
    compile' (CtorSrcExp ctor args _) =
      do args_th <- compile args
         return $ applyTHExp (TH.ConE 'SourceCtor)
           [applyTHExp (TH.ConE $ ctor_th_name ctor) args_th]
    compile' (TupleSrcExp sexps _) =
      do sexps_th <- compile sexps
         return $ applyTHExp (TH.ConE 'SourceCtor)
           [mkTupleBodyTHExp sexps_th]
    compile' (FileSrcExp filename fmt tp) = compileFileSource filename fmt tp
    compile' (ListCompSrcExp expr arms tp) = do
      expr_th <- compile expr
      map_pat <- compileArmPat arms
      let zip_srcs (lExpr, lTyp) rArm@(ListCompArm _ rExp) = do
            rExpr <- compileArmExpr rArm
            lName <- lift $ lift $ TH.newName "l"
            rName <- lift $ lift $ TH.newName "r"
            let rTyp = getTypeOf rExp
            typ   <- zipTypes lTyp rTyp
            typTH <- TH.AppT (TH.ConT ''Source) <$> compile typ
            let innerFun = applyTHExp (TH.ConE 'SourceBind)
                  [ TH.LamE [TH.VarP rName]
                    (TH.AppE (TH.VarE 'dvToSource)
                       (applyTHExp (TH.VarE 'zipDV)
                         [TH.VarE lName, TH.VarE rName]))
                  , rExpr
                  ]
                outerExp = applyTHExp (TH.ConE 'SourceBind)
                  [ TH.LamE [TH.VarP lName] innerFun
                  , lExpr
                  ]
            return ( TH.SigE outerExp typTH
                   , typ
                   )
      zipped_th <- let (a@(ListCompArm _ aExp):as) = arms in do
        aExpr  <- compileArmExpr a
        let aTyp = getTypeOf aExp
        foldM zip_srcs (aExpr, aTyp) as
      tp_th <- compile tp
      let src_tp = TH.AppT (TH.ConT ''Source) tp_th
      return $ flip TH.SigE src_tp $ applyTHExp (TH.ConE 'SourceBind)
        [ applyTHExp (TH.VarE 'mapSource)
            [ TH.LamE [map_pat] expr_th ]
        , fst zipped_th
        ]

instance Compilable (GPriorStmt Rewritten) TH.Exp where
  compile stmt = withCompileCtx stmt $ compile' stmt where
    compile' (GPriorStmt lhs rhs) = do
      lhs_th <- compile lhs
      rhs_th <- compile rhs
      embedM $ [| do { src <- liftIO (interp__'source $(return lhs_th))
                     ; return (interp__'sample $(return rhs_th) src interp__'return)
                     } |]


--
-- ** Statements and Top-level Forms
--

instance Compilable (StmtCase Rewritten) TH.Match where
  compile (StmtCase patt body _) = do
    patt_th <- compile patt
    body_th <- compile body
    return $ TH.Match patt_th (TH.NormalB body_th) []

instance Compilable (ExpCase Rewritten) TH.Match where
  compile (ExpCase patt body _ _) = do
    patt_th <- compile patt
    body_th <- compile body
    return $ TH.Match patt_th (TH.NormalB body_th) []

instance Compilable (CompiledPattern Rewritten) TH.Pat where
  compile p = withCompileCtx p $ compile' p where
    compile' (CompiledBasicPattern pat) = return $ compileVarPat pat
    compile' (CompiledCtorPat ctor patts _) = do
      let patts_th = map compileVarPat patts
      return $ TH.ConP (ctor_th_name ctor) patts_th
    compile' (CompiledTuplePat patts _) =
      return (mkTupleTHPat (map compileVarPat patts))
    compile' (CompiledLitPat (IntegerLit i) _) = return $ TH.LitP $ TH.IntegerL i
    compile' (CompiledLitPat (RationalLit r) _) = return $ TH.LitP $ TH.RationalL r

-- We compile v-expressions into expresssions that build them and patterns that
-- destruct them. For v-expressions that are "generated", which includes
-- wildcards and lifted expression, we need to generate them in a statement
-- context, by calling interp__'vwild or interp__'vlift, respectively, so we
-- here just generate fresh TH variables and return a list of those variables as
-- well as the interp method needed to generate them, which should have type
--
-- (GVExpr repr a -> GStmt repr b) -> GStmt repr b
instance Compilable (VExp Rewritten) ((TH.Exp, TH.Exp -> TH.Exp), [(TH.Name, TH.Exp)]) where
  compile ve = withCompileCtx ve $ runWriterT $ go ve where
    go :: VExp Rewritten -> WriterT [(TH.Name, TH.Exp)] Compile (TH.Exp, TH.Exp -> TH.Exp)
    go (VarVExp n True _) = do
      let expr = TH.VarE (TH.mkName ("v__" ++ T.unpack n))
          pat = TH.VarP (TH.mkName (T.unpack n))
      return (expr, TH.LamE [pat])
    go (VarVExp n False _) = do
      let n_th = TH.mkName ("v__" ++ T.unpack n)
          expr = TH.VarE n_th
          pat = TH.VarP (TH.mkName (T.unpack n))
      tell [(n_th, TH.VarE 'interp__'vwild)]
      return (expr, TH.LamE [pat])
    go (WildVExp _) = do
      n_th <- lift $ embedM $ TH.newName "wild"
      tell [(n_th, TH.VarE 'interp__'vwild)]
      return (TH.VarE n_th, TH.LamE [TH.VarP n_th])
    go (EmbedVExp e _) = do
      n_th <- lift $ embedM $ TH.newName "v__"
      e_th <- lift $ compile e
      tell [(n_th, TH.AppE (TH.VarE 'interp__'vlift) e_th)]
      return (TH.VarE n_th, TH.LamE [TH.VarP n_th])
    go (SigVExp v _) = do
      go v
    go (TupleVExp vs _) = do
      (exprs, vars) <- fmap unzip $ mapM go vs
      fresh_vars <- sequence [ lift $ embedM (TH.newName "t") | _ <- vs ]
      scrut_var <- lift $ embedM (TH.newName "scrut")
      let exprsI = TH.AppE (TH.VarE 'interp__'vInjTuple) (mkTupleBodyTHExp exprs)
          mkBody [] [] rest = rest
          mkBody (p:ps) (t:ts) rest =
            applyTHExp (t (mkBody ps ts rest)) [ TH.VarE p ]
          mkBody _ _ _ = error "unreachable"
      return ( exprsI
             , \ body ->
                 TH.LamE [TH.VarP scrut_var] $
                   applyTHExp (TH.VarE 'interp__'projTupleStmt)
                     [ TH.VarE scrut_var
                     , TH.LamE [mkTupleBodyTHPat (map TH.VarP fresh_vars)]
                       (mkBody fresh_vars vars body)
                     ]
             )
    go xs = error ("FIXME in Compilable VExp: " ++ show xs)

-- | Compile the pattern for the current model sub-case to a TH expression,
-- whose value is the return value for the current sub-case
compilePattInterp :: Compile TH.Exp
compilePattInterp = getModelSubCasePattern >>= helper where
  go' (VarCPat x _) =
    return $ TH.VarE $ TH.mkName $ T.unpack x
  go' (WildCPat _) =
    error "Unexpected wildcard pattern in model subcase!"
  helper :: Pattern Rewritten -> Compile TH.Exp
  helper (CompiledBasicPattern pat) = go' pat
  helper (CompiledCtorPat ctor patts _) =
    mkADTCtorTHExp ctor <$> mapM go' patts
  helper (CompiledTuplePat patts _) = do
    patts_th <- mkTupleBodyTHExp <$> mapM go' patts
    return (TH.AppE (TH.VarE 'interp__'injTuple) patts_th)
  helper (CompiledLitPat (IntegerLit i) _) = return $ TH.LitE $ TH.IntegerL i
  helper (CompiledLitPat (RationalLit r) _) = return $ TH.LitE $ TH.RationalL r

instance Compilable (Stmt Rewritten) TH.Exp where
  compile stmt = withCompileCtx stmt $ go stmt where
    go ReturnStmt = do
      rs <- compilePattInterp
      return $ TH.AppE (TH.VarE 'interp__'return) rs
    go (SampleStmt lhs rhs body) = do
      ((lhs_th, pat_th), vexp_vars_gens) <- compile lhs
      rhs_th  <- compile rhs
      body_th <- compile body
      let body_lam = pat_th body_th
      return $
        flip (foldr $ \ (var, gen_exp) expr ->
               TH.AppE gen_exp $ TH.LamE [TH.VarP var] expr)
        vexp_vars_gens $
        applyTHExp (TH.VarE 'interp__'sample) [rhs_th, lhs_th, body_lam]
    go (LetStmt x rhs body) = do
      let lhs_th = TH.VarP (TH.mkName (T.unpack x))
      rhs_th <- compile rhs
      body_th <- compile body
      return $ TH.LetE [TH.ValD lhs_th (TH.NormalB rhs_th) []] body_th
    go (CaseStmt e cs) =
      compileInterpCase e cs

compileBranch :: ModelSubCase Rewritten -> Compile [TH.Exp]
compileBranch (ModelSubCase (CompiledCtorPat _ ps _) prob_e stmt) = do
  prob <- case prob_e of
    Nothing -> return $ TH.AppE (TH.VarE 'interp__'rational) (TH.LitE (TH.RationalL 1.0))
    Just e  -> compile e
  let pat = CompiledTuplePat ps (TupleType [])
  pat_th <- compileVExprPatternInterp pat
  body_th <- withModelSubCasePattern pat $ compile stmt
  body <- embedM [| interp__'mkDist $(return (pat_th body_th)) |]
  return [ prob, body ]
compileBranch _ =
  error "Language.Grappa.Frontend.Compile.compileBranch: unreachable"

-- | We need to convert all pattern-matches into calls to the
-- catamorphism over the ADT we've created; to do this, we need to
-- know the order of the constructors. We loop over the constructors
-- listed in the TypeNameInfo in order and find the matching case.
-- TODO: handle more complicated cases, like nested patterns!
compileCtorCases :: TypeNameInfo -> [ModelSubCase Rewritten] -> Compile TH.Exp
compileCtorCases _ [cs@(ModelSubCase (CompiledCtorPat n _ _) _ _)] = do
  let ctor_name = ctor_th_name n
      interp_ctor = TH.mkName ("interp__ctorDist__" ++ TH.nameBase ctor_name)
  [_, body_th] <- compileBranch cs
  let dist = applyTHExpInterp (TH.VarE interp_ctor) [body_th]
  embedM [| (\ v -> interp__'sample $(return dist) v interp__'return) |]
compileCtorCases info cs = do
  let findConstructor n = case [ c | c@(ModelSubCase (CompiledCtorPat n' _ _) _ _) <- cs
                                   , ctor_th_name n' == adt_ctor_th_name n
                                   ] of
                             [c] -> return c
                             []  -> fail ("Unable to find case for " ++ show n)
                             _   -> fail "Unable to handle overlapping cases"
  case tn_ctors info of
    Nothing -> fail "Pattern-matching over a non-ADT"
    Just ts -> do
      pats <- mapM findConstructor ts
      args <- concat <$> mapM compileBranch pats
      let interp_adt = TH.mkName ("interp__adtDist__" ++
                                  TH.nameBase (tn_th_name info))
      let dist = applyTHExpInterp (TH.VarE interp_adt) args
      embedM [| (\ v -> interp__'sample $(return dist) v interp__'return) |]

-- * Compiling interpreted patterns

-- Function arguments at this point are only ever going to be
-- variables, so we can ignore all other patterns here
compileFunctionArgInterp :: Pattern Rewritten -> Compile TH.Pat
compileFunctionArgInterp (CompiledBasicPattern pat) =
  return $ compileVarPat pat
compileFunctionArgInterp pat =
  fail ("Unexpected top-level pattern: " ++ show pat)

compileVarPat :: CompiledVarPattern Rewritten -> TH.Pat
compileVarPat (VarCPat x _) = TH.VarP $ TH.mkName $ T.unpack x
compileVarPat (WildCPat _) = TH.WildP

compileVarPatExp :: CompiledVarPattern Rewritten -> TH.Exp
compileVarPatExp (VarCPat x _) = TH.VarE $ TH.mkName $ T.unpack x
compileVarPatExp (WildCPat _) = error "unexpected wildcard"

-- V-expression patterns are pretty straightforward, but sometimes
-- we'll need to unwrap the outer ADT tuple layer and sometimes we
-- won't---hence the bool, which is True if we need a tuple
-- projection.
compileVExprPatternInterp :: Pattern Rewritten -> Compile (TH.Exp -> TH.Exp)
compileVExprPatternInterp patt = withCompileCtx patt $ go patt where
  go (CompiledBasicPattern pat) = do
    pat' <- go' pat
    return $ TH.LamE [pat']
  go (CompiledCtorPat _ _ _) = do
    fail "Unsure of how to compile constructors in this context"
  go (CompiledTuplePat patts _) = do
    tup <- embedM (TH.newName "tup")
    patts_th <- mkTupleBodyTHPat <$> mapM go' patts
    return $ \ body ->
      TH.LamE [TH.VarP tup] $
        applyTHExp (TH.VarE 'interp__'vProjTuple)
          [ TH.VarE tup, TH.LamE [patts_th] body]
  go (CompiledLitPat (IntegerLit i) _) =
    return $ TH.LamE [TH.LitP (TH.IntegerL i)]
  go (CompiledLitPat (RationalLit r) _) =
    return $ TH.LamE [TH.LitP (TH.RationalL r)]
  go' (VarCPat x _) =
    return $ TH.VarP $ TH.mkName $ ("v__" ++ T.unpack x)
  go' (WildCPat _) = return TH.WildP

instance Compilable (ModelCase Rewritten) TH.Clause where
  compile (ModelCase patts sub_cases) = do
    patts_th <- mapM compileFunctionArgInterp patts
    sub_cases_th <- case sub_cases of
      [] -> fail "Error: no subcases in model"
      ModelSubCase (CompiledCtorPat (CtorInfo { ctor_type = typ }) _ _) _ _ : _ ->
        case typ of
          TopType _ _ _ (ADTType info _) ->
            compileCtorCases info sub_cases
          TopType _ _ _ t ->
            fail ("Return type of constructor doesn't name an ADT:" ++ show t)
      [ModelSubCase pat _ ss] -> withModelSubCasePattern pat $ do
        pat_th <- compileVExprPatternInterp pat
        body_th <- compile ss
        return $ pat_th body_th
      cs -> fail ("Unsure how to handle " ++ show cs)
    body_th <-
      embedM $ [| interp__'mkDist $(return sub_cases_th) |]
    fun_th <- F.foldrM (\ pat expr ->
                          embedM [| interp__'lam (\ $(return pat) -> $(return expr)) |])
                body_th patts_th
    return (TH.Clause [] (TH.NormalB fun_th) [])

compileSubCases :: [ModelSubCase Rewritten] -> Compile TH.Exp
compileSubCases sub_cases = fmap (TH.AppE (TH.VarE 'interp__'mkDist)) $ case sub_cases of
  [] -> fail "Error: no subcases in model"
  (ModelSubCase (CompiledCtorPat (CtorInfo { ctor_type = typ }) _ _) _ _ : _) ->
        case typ of
          TopType _ _ _ (ADTType info _) ->
            compileCtorCases info sub_cases
          TopType _ _ _ t ->
            fail ("Return type of constructor doesn't name an ADT: " ++ show t)
  [ModelSubCase pat _ ss] -> withModelSubCasePattern pat $ do
        pat_th <- compileVExprPatternInterp pat
        body_th <- compile ss
        return $ pat_th body_th
  cs -> fail ("Unsure how to handle " ++ show cs)

mkInterpLam :: [CompiledVarPattern Rewritten] -> TH.Exp -> Compile TH.Exp
mkInterpLam [] e = return e
mkInterpLam (VarCPat i _:ps) e = do
  let pat = TH.VarP (TH.mkName (T.unpack i))
  expr_th <- mkInterpLam ps e
  embedM [| interp__'lam (\ $(return pat) -> $(return expr_th)) |]
mkInterpLam (WildCPat _:ps) e = do
  let pat = TH.WildP
  expr_th <- mkInterpLam ps e
  embedM [| interp__'lam (\ $(return pat) -> $(return expr_th)) |]

instance Compilable (Decl Rewritten) [TH.Dec] where
  compile (ModelDecl {}) = do
    error "we should compile all ModelDecls to FunDecls via pattern-matching conversion"

  compile d@(FunDecl nm annot [FunCase pats expr]) =
    withLocalCompileEnv $ withCompileCtx d $ withCurrentFunction nm $
    do let nm_th = TH.mkName $ T.unpack $ interpIdent nm
       tp_th <- compile annot
       addResolvedGName nm $ ResGName { gname_ident = nm,
                                        gname_th_name = nm_th,
                                        gname_type = annot,
                                        gname_fixity = TH.defaultFixity }
       Just fix_th <- compile_fix_parameter <$> get
       expr_th <- compile expr
       body_th <- mkInterpLam pats expr_th
       let body_fix_th =
             TH.AppE (TH.VarE 'interp__'fix)
             (TH.LamE [TH.VarP fix_th] body_th)
       return [ TH.SigD nm_th tp_th
              , TH.FunD nm_th [TH.Clause [] (TH.NormalB body_fix_th) []]
              ]

  compile (FunDecl {}) =
    error "Function with more than one top-level case (we should rewrite these away)"

  compile (SourceDecl name _ src_exp) =
    do src_exp_th <- compile src_exp
       return [ TH.ValD (TH.VarP $ TH.mkName $ T.unpack name)
                (TH.NormalB src_exp_th) [] ]

  compile (MainDecl (GPriorStmt src_expr model_expr)
            (InfMethod { infName = meth , infParams = es })) =
    do model_th <- compile model_expr
       src_expr_th <- compile src_expr
       es_th <- compile es
       let mainExpr =
             applyTHExp (TH.VarE (imRunFunc meth)) $
             es_th ++ src_expr_th : replicate (imModelCopies meth) model_th
       embedM $ [d| main :: IO ()
                    main = $(return mainExpr) |]


--
-- * Quasi-quoter for posterior expressions
--

compileGPostInterp :: String -> TH.Q TH.Exp
compileGPostInterp str = runCompile $ do
  parsed_e <- embedM $ parseGPrior startPos str
  resolved_e <- embedM $ resolve parsed_e
  let fixed_e = fixupOps resolved_e
  checked_e <- embedM $ typeCheck fixed_e ()
  rewritten <- embedM $ rewriteMatches checked_e
  compile rewritten

gpost :: TH.QuasiQuoter
gpost = TH.QuasiQuoter
  { TH.quoteExp  = compileGPostInterp
  , TH.quotePat  = const (error "No gprior quasi-quoter for patterns")
  , TH.quoteType = const (error "No gprior quasi-quoter for types")
  , TH.quoteDec  = const (error "No top-level gprior quasi-quoter")
  }


--
-- * Top-level Compiler
--

compileGrappa :: String -> TH.Q [TH.Dec]
compileGrappa str =
  runCompile $
  do parsed_ds <- embedM $ parseDecls startPos str
     liftM concat $ forM parsed_ds $ \parsed_d ->
       do resolved_d <- embedM $ resolve parsed_d
          let fixed_d = fixupOps resolved_d
          checked_d <- embedM $ typeCheck fixed_d ()
          rewritten <- embedM $ rewriteMatches checked_d
          compile rewritten

grappa :: TH.QuasiQuoter
grappa =
  TH.QuasiQuoter
  { TH.quoteExp = \_ -> error "No Grappa quasi-quoter for expressions",
    TH.quotePat = \_ -> error "No Grappa quasi-quoter for patterns",
    TH.quoteType = \_ -> error "No Grappa quasi-quoter for types",
    TH.quoteDec = compileGrappa }
