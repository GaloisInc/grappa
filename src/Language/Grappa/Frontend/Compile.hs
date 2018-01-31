{-# LANGUAGE DataKinds, TypeFamilies, EmptyDataDecls, GADTs, TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE ParallelListComp, ViewPatterns #-}

module Language.Grappa.Frontend.Compile where

import System.IO
import Data.Proxy
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
import Language.Grappa.Frontend.TypeCheck
import Language.Grappa.Frontend.DataSource
import Language.Grappa.Frontend.Errors()
import Language.Grappa.Inference
import Language.Grappa.Interp
import Language.Grappa.GrappaInternals

--
-- Monad for the Whole Grappa Compiler
--

data CompileContext = CompileCtxExp (Exp Typed)
                    | CompileCtxVExp (VExp Typed)
                    | CompileCtxPrExp (SourceExp Typed)
                    | CompileGenExp (GenExp Typed)
                    | CompileListCompArm (ListCompArm Typed)
                    | CompileCtxStmt (Stmt Typed)
                    | CompileCtxGPStmt (GPriorStmt Typed)
                    | CompileCtxPattern (Pattern Typed)
                    | CompileCtxDecl (Decl Typed)
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
instance HasCompileContext (Exp Typed) where
  mkCompileContext = CompileCtxExp
instance HasCompileContext (VExp Typed) where
  mkCompileContext = CompileCtxVExp
instance HasCompileContext (SourceExp Typed) where
  mkCompileContext = CompileCtxPrExp
instance HasCompileContext (GenExp Typed) where
  mkCompileContext = CompileGenExp
instance HasCompileContext (ListCompArm Typed) where
  mkCompileContext = CompileListCompArm
instance HasCompileContext (Stmt Typed) where
  mkCompileContext = CompileCtxStmt
instance HasCompileContext (GPriorStmt Typed) where
  mkCompileContext = CompileCtxGPStmt
instance HasCompileContext (Pattern Typed) where
  mkCompileContext = CompileCtxPattern
instance HasCompileContext (Decl Typed) where
  mkCompileContext = CompileCtxDecl

-- | The Grappa compilation errors
data GrappaError = GErrorParse ParseError
                 | GErrorResolve ResolveError
                 | GErrorEmit EmitError
                 | GErrorTypeCheck TypeError
                 | GErrorMisc String
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
  pretty (GErrorContext err ctx) =
    PP.pretty err PP.<$$>
    PP.text "In compiling" PP.<$$> PP.nest 2 (PP.pretty ctx)

-- | The type of environments for compilation to TH
data CompileEnv =
  CompileEnv { compile_emit_env :: EmitEnv,
               compile_res_env :: ResolveEnv,
               compile_current_function :: Maybe Ident,
               compile_fix_parameter :: Maybe TH.Name,
               compile_model_subcase_vpatt :: Maybe (Pattern Typed),
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
getModelSubCasePattern :: Compile (Pattern Typed)
getModelSubCasePattern =
  do maybe_patt <- compile_model_subcase_vpatt <$> get
     case maybe_patt of
       Just patt -> do
         return patt
       Nothing -> error "getModelSubCasePattern: missing model case pattern!"

-- | Run a 'Compile' computation using a given model case pattern
withModelSubCasePattern :: Pattern Typed -> Compile a -> Compile a
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

-- FIXME HERE: revisit the next 13 functions, fixing up their names to better
-- reflect what they do and maybe use them more in the code below

-- | Build a TH expression of type @'ADT' adt 'Id'@ for a Grappa constructor of
-- @adt@ and its argument expressions
mkADTCtorTHExp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkADTCtorTHExp ctor args_th =
  if ctor_is_adt ctor then
    applyTHExp (TH.ConE 'ADT) [applyTHExp (TH.ConE $ ctor_th_name ctor) $
                               map mkIdTHExp args_th]
  else
    error "mkADTCtorTHExp: non-ADT constructor"

-- | Build a TH expression of type @adt ('GExpr' repr) (ADT adt)@ for a Grappa
-- constructor of @adt@ and its argument expressions
mkADTCtorTHExpInterp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkADTCtorTHExpInterp ctor args_th =
  if ctor_is_adt ctor then
    applyTHExp (TH.ConE $ ctor_th_name ctor) args_th
  else
    error "mkADTCtorTHExp: non-ADT constructor"

-- | Build a TH expression of type @'GrappaData' ('ADT' adt 'Id')@ for a Grappa
-- constructor of @adt@ and its argument expressions
mkCtorGrappaDataTHExp :: CtorInfo -> [TH.Exp] -> TH.Exp
mkCtorGrappaDataTHExp ctor args_th =
  if ctor_is_adt ctor then
    applyTHExp (TH.ConE 'VADT) [applyTHExp (TH.ConE $ ctor_th_name ctor) args_th]
  else
    error "mkCtorGrappaDataTHExp: non-ADT constructor"


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

-- | Like 'mkCtorLamTHExp' but building an interpretation instead of just a raw
-- TH expression
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

-- | Build a TH expression for a Grappa tuple inside a 'GrappaData'
mkTupleGrappaDataTHExp :: [TH.Exp] -> TH.Exp
mkTupleGrappaDataTHExp exps =
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

-- | Compile a Grappa identifier to a 'TH.Name'
compileIdent :: Ident -> TH.Name
compileIdent var = TH.mkName $ T.unpack var

-- | Compile an identifier that represents a 'GVExpr' variable to a 'TH.Name'
-- distinct from the one returned by the normal 'compile', by prepending "v__"
compileVIdent :: Ident -> TH.Name
compileVIdent var = TH.mkName $ "v__" ++ (T.unpack var)

instance Compilable (Name Typed) TH.Exp where
  compile (LocalName x) = do
    -- If this isn't set, then we're doing something wrong
    Just curr <- compile_current_function <$> get
    Just self <- compile_fix_parameter <$> get
    return $ TH.VarE $ if curr == x then self else compileIdent x
  compile (GlobalName nm) = return $ TH.VarE $ gname_th_name nm
  compile (CtorName ctor) =
    return $ mkCtorLamTHExpInterp ctor []

instance Compilable (Exp Typed) TH.Exp where
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
    go (AppExp (NameExp (CtorName ctor) _) args _) =
      mkCtorLamTHExpInterp ctor <$> compile args
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
      return $ TH.LetE [TH.ValD (TH.VarP $ compileIdent n)
                        (TH.NormalB lhs_th) []] rhs_th
    go (CaseExp scrut cases _) =
      compileCaseExp scrut cases
    go (ModelExp cases _) =
      do n_th <- embedM $ TH.newName "v__"
         body_th <- compileModelBody n_th cases
         return $ applyTHExp (TH.VarE 'interp__'mkDist)
           [TH.LamE [TH.VarP n_th] body_th]
    go (IfExp c t e _) = do
      c_th <- compile c
      t_th <- compile t
      e_th <- compile e
      return $ applyTHExp (TH.VarE 'interp__'ifThenElse) [c_th, t_th, e_th]
    go (FunExp fun_case _) = compileFunExp [fun_case]
    go (ListExp enabled _) = notEnabled enabled
    go (ParensExp enabled _) = notEnabled enabled
    go (OpExp enabled _ _ _) = notEnabled enabled

-- | "Raw", non-interpreted compilation of expressions, for, e.g., parameters to
-- inference methods
rawCompileExpr :: Exp Typed -> Compile TH.Exp
rawCompileExpr e = withCompileCtx e $ compile' e where
  compile' :: Exp Typed -> Compile TH.Exp
  compile' (NameExp (LocalName x) _) =
    return $ TH.VarE $ compileIdent x
  compile' (NameExp (GlobalName nm) _) =
    case gname_raw_th_name nm of
      Just th_nm -> return $ TH.VarE th_nm
      Nothing ->
        throwError $ GErrorMisc $
        "Cannot compile identifier in \"raw\" context: "
        ++ T.unpack (gname_ident nm)
  compile' (NameExp (CtorName ctor) _) = return $ mkCtorLamTHExp ctor []
  compile' (LiteralExp (IntegerLit i) _tp) =
    return $ TH.LitE $ TH.IntegerL i
  compile' (LiteralExp (RationalLit r) _tp) =
    return $ TH.LitE $ TH.RationalL r
  compile' (SigExp _expr _tp) =
    -- FIXME: need compileRawType here
    throwError $ GErrorMisc $ "Cannot (yet) compile types in \"raw\" context"
  compile' (AppExp (NameExp (CtorName ctor) _) args _) =
    mkCtorLamTHExp ctor <$> mapM compile' args
  compile' (AppExp f args _) =
    do f_th <- compile' f
       args_th <- mapM compile' args
       return $ applyTHExp f_th args_th
  compile' (TupleExp exps _) =
    mkTupleTHExp <$> mapM compile' exps
  compile' (OpExp enabled _ _ _) = notEnabled enabled
  compile' (ParensExp enabled _) = notEnabled enabled
  compile' (ListExp enabled _) = notEnabled enabled
  compile' (LetExp n _ lhs rhs _) =
    do lhs_th <- compile' lhs
       rhs_th <- compile' rhs
       return $ TH.LetE [TH.ValD (TH.VarP $ compileIdent n)
                         (TH.NormalB lhs_th) []] rhs_th
  compile' (CaseExp _scrut _cases _) =
    throwError $ GErrorMisc $
    "Cannot compile case expressions in \"raw\" context"
  compile' (ModelExp _cases _) =
    throwError $ GErrorMisc $
    "Cannot compile model expressions in \"raw\" context"
  compile' (IfExp c_e t_e e_e _) = do
    c_th <- compile' c_e
    t_th <- compile' t_e
    e_th <- compile' e_e
    return $ TH.CondE c_th t_th e_th
  compile' (FunExp (FunCase _pats _expr) _) =
    throwError $ GErrorMisc $
    "Cannot compile lambda expressions in \"raw\" context"


--
-- ** Pattern-Matching Expression Compilation
--

-- | Compile a tuple pattern with the given names for the pattern variables
compileTuplePatt :: [TH.Name] -> TH.Pat
compileTuplePatt [] = TH.ConP 'Tuple0 []
compileTuplePatt [a] = TH.ConP 'Tuple1 [TH.VarP a]
compileTuplePatt ns@[_,_] = TH.ConP 'Tuple2 (map TH.VarP ns)
compileTuplePatt ns@[_,_,_] = TH.ConP 'Tuple3 (map TH.VarP ns)
compileTuplePatt ns@[_,_,_,_] = TH.ConP 'Tuple4 (map TH.VarP ns)
compileTuplePatt (a:b:c:d:e:ns') =
  TH.ConP 'TupleN [TH.VarP a, TH.VarP b, TH.VarP c, TH.VarP  d, TH.VarP e,
                   compileTuplePatt ns']

-- | Compile a single branch of a @case@ expression, that matches a sequence of
-- arguments (bound to TH names) with a sequence of patterns, into a 'GMatch'
compileMatchBranch :: [TH.Name] -> [Pattern Typed] -> TH.Exp -> TH.Q TH.Exp
compileMatchBranch [] [] body = [| interp__'matchBody $(return body) |]
compileMatchBranch (n:ns) (VarPat x _:patts) body =
  do body_th <- compileMatchBranch ns patts body
     return $ TH.LetE [TH.ValD (TH.VarP $ compileIdent x)
                       (TH.NormalB $ TH.VarE n) []] body_th
compileMatchBranch (_:ns) (WildPat _:patts) body =
  compileMatchBranch ns patts body
compileMatchBranch (n:ns) (TuplePat arg_patts _:patts) body =
  do sub_ns <- mapM (const $ TH.newName "arg_") arg_patts
     body_th <-
       TH.LamE [compileTuplePatt sub_ns] <$>
       compileMatchBranch (sub_ns ++ ns) (arg_patts ++ patts) body
     [| interp__'matchTuple $(TH.varE n) $(return body_th) |]
compileMatchBranch (n:ns) (CtorPat ctor ctor_patts _:patts) body =
  do arg_ns <- mapM (const $ TH.newName "arg_") ctor_patts
     let proxy =
           applyTHExp (TH.ConE (ctor_th_name ctor)) $
           replicate (ctorArity ctor) (TH.ConE 'Proxy)
         matcher =
           TH.VarE $ TH.mkName $
           "ctorMatcher__" ++ TH.nameBase (ctor_th_name ctor)
     body_th <-
       TH.LamE [TH.ConP (ctor_th_name ctor) (map TH.VarP arg_ns)] <$>
       compileMatchBranch (arg_ns ++ ns) (ctor_patts ++ patts) body
     [| interp__'matchADT $(TH.varE n) $(return proxy)
      $(return matcher) $(return body_th) |]
compileMatchBranch (n:ns) (LitPat lit _:patts) body =
  do lit_th <-
       case lit of
         IntegerLit i -> [| interp__'integer $(TH.litE (TH.IntegerL i)) |]
         RationalLit r -> [| interp__'rational $(TH.litE (TH.RationalL r)) |]
     body_th <- compileMatchBranch ns patts body
     [| interp__'matchGuard
      (interp__'app (interp__'app interp__'eq'eq $(TH.varE n)) $(return lit_th))
      $(return body_th) |]
compileMatchBranch (n:ns) (SigPat patt _:patts) body =
  compileMatchBranch (n:ns) (patt:patts) body
compileMatchBranch (_:_) [] _ =
  error "Compiler error: mismatched number of names and patterns"
compileMatchBranch [] (_:_) _ =
  error "Compiler error: mismatched number of names and patterns"


-- | Combine a list of expressions, that are the result of compiling a list of
-- case expression branches, into a single 'GMatch' expression
combineMatchBranches :: [TH.Exp] -> TH.Q TH.Exp
combineMatchBranches [] = [| interp__'matchFail |]
combineMatchBranches (match:matches') =
  [| interp__'matchDisj $(return match) $(combineMatchBranches matches') |]

-- | Compile a case expression with a single scrutinee and a list of cases
compileCaseExp :: Exp Typed -> [ExpCase Typed] -> Compile TH.Exp
compileCaseExp scrut cases =
  do
    -- Generate a TH name for the result of the scrutinee
    n_th <- embedM $ TH.newName "scrutinee_"
    -- Compile the scrutinee and each branch of the case expression
    scrut_th <- compile scrut
    cases_th <-
      mapM (\(ExpCase patt body _ _) ->
             do body_th <- compile body
                embedM $ compileMatchBranch [n_th] [patt] body_th) cases
    -- Return the case expression inside a let-binding for the scrutinee
    body_th <-
      embedM $ [| interp__'match $(combineMatchBranches cases_th) |]
    return $ TH.LetE [TH.ValD (TH.VarP n_th) (TH.NormalB scrut_th) []] body_th

-- | Compile a pattern-matching function definition or declaration to a 'GExpr'
compileFunExp :: [FunCase Typed] -> Compile TH.Exp
compileFunExp [] = error "compileFunExp: empty list of function cases!"
compileFunExp cases@(FunCase head_patts _:_) =
  do
    -- Generate names for all the arguments
    ns_th <- embedM $ mapM (const $ TH.newName "x_") head_patts
    -- Compile each branch of the pattern-matching function
    cases_th <-
      mapM (\(FunCase patts body) ->
             do body_th <- compile body
                embedM $ compileMatchBranch ns_th patts body_th) cases
    -- Return the case expression inside a lambda for all the arguments
    body_th <-
      embedM $ [| interp__'match $(combineMatchBranches cases_th) |]
    return $ foldr (\n e ->
                     TH.AppE (TH.VarE 'interp__'lam) $
                     TH.LamE [TH.VarP n] e) body_th ns_th


--
-- ** Pattern-Matching Over V-Expressions
--

-- | Compile a single branch of a @case@ statement over, that matches a sequence of
-- arguments (bound to TH names) with a sequence of patterns, into a 'GVMatchOne'
compileVMatchBranch :: [TH.Name] -> [Pattern Typed] -> TH.Exp -> TH.Q TH.Exp
compileVMatchBranch [] [] body = [| interp__'vmatchBody $(return body) |]
compileVMatchBranch (n:ns) (VarPat x _:patts) body =
  do body_th <- compileVMatchBranch ns patts body
     return $ TH.LetE [TH.ValD (TH.VarP $ compileVIdent x)
                       (TH.NormalB $ TH.VarE n) []] body_th
compileVMatchBranch (_:ns) (WildPat _:patts) body =
  compileVMatchBranch ns patts body
compileVMatchBranch (n:ns) (TuplePat arg_patts _:patts) body =
  do sub_ns <- mapM (const $ TH.newName "arg_") arg_patts
     body_th <-
       TH.LamE [compileTuplePatt sub_ns] <$>
       compileVMatchBranch (sub_ns ++ ns) (arg_patts ++ patts) body
     [| interp__'vmatchTuple $(TH.varE n) $(return body_th) |]
compileVMatchBranch (n:ns) (CtorPat ctor ctor_patts _:patts) body =
  do arg_ns <- mapM (const $ TH.newName "arg_") ctor_patts
     let proxy =
           applyTHExp (TH.ConE (ctor_th_name ctor)) $
           replicate (ctorArity ctor) (TH.ConE 'Proxy)
         matcher =
           TH.VarE $ TH.mkName $
           "ctorMatcher__" ++ TH.nameBase (ctor_th_name ctor)
     body_th <-
       TH.LamE [TH.ConP (ctor_th_name ctor) (map TH.VarP arg_ns)] <$>
       compileVMatchBranch (arg_ns ++ ns) (ctor_patts ++ patts) body
     [| interp__'vmatchADT $(TH.varE n) $(return proxy)
      $(return matcher) $(return body_th) |]
compileVMatchBranch (n:ns) (LitPat lit _:patts) body =
  do lit_th <-
       case lit of
         IntegerLit i -> [| interp__'integer $(TH.litE (TH.IntegerL i)) |]
         RationalLit r -> [| interp__'rational $(TH.litE (TH.RationalL r)) |]
     body_th <- compileVMatchBranch ns patts body
     [| interp__'vmatchGuard
      (interp__'app (interp__'app interp__'eq'eq $(TH.varE n)) $(return lit_th))
      $(return body_th) |]
compileVMatchBranch ns (SigPat patt _:patts) body =
  compileVMatchBranch ns (patt:patts) body
compileVMatchBranch (_:_) [] _ =
  error "Compiler error: mismatched number of names and patterns"
compileVMatchBranch [] (_:_) _ =
  error "Compiler error: mismatched number of names and patterns"


-- | Compile a sequence of 'ModelCase's into a 'GVMatch' pattern-matching
-- statement over v-expressions
compileModelCases :: TH.Name -> [ModelCase Typed] -> Compile TH.Exp
compileModelCases _ [] = embedM [| interp__'vmatchFail |]
compileModelCases n_th (ModelCase patt prob_exp body : cases) =
  do prob_exp_th <- compile prob_exp
     body_th <- withModelSubCasePattern patt $ compile body
     case_th <- embedM $ compileVMatchBranch [n_th] [patt] body_th
     cases_th <- compileModelCases n_th cases
     embedM [| interp__'vmatchDisj $(return prob_exp_th) $(return case_th)
             $(return cases_th) |]

-- | Compile the body of a @model@ expression to a 'GStmt'
compileModelBody :: TH.Name -> [ModelCase Typed] -> Compile TH.Exp
compileModelBody n_th [ModelCase patt _ body] =
  -- Special case: for only a single case, use interp__'vmatch1
  do body_th <- withModelSubCasePattern patt $ compile body
     case_th <- embedM $ compileVMatchBranch [n_th] [patt] body_th
     embedM [| interp__'vmatch1 $(return case_th) |]
compileModelBody n_th cases =
  do body_th <- compileModelCases n_th cases
     embedM [| interp__'vmatch $(return body_th) |]


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
        FileVarName   nm -> TH.varE (compileIdent nm)
  tp_th <- compile tp
  fmt_th <- mkFormatTHExp (T.unpack fmt)
  embedM [|
        ($(TH.conE ctor)
         (SourceFile
          $(file_th)
          $(return fmt_th)))
        :: Source $(return tp_th)
        |]

compileArmExpr :: ListCompArm Typed -> Compile TH.Exp
compileArmExpr _ = error "FIXME"

compileArmPat :: [ListCompArm Typed] -> Compile TH.Pat
compileArmPat _ = error "FIXME"
  -- do
  --   let pats = [ (pat, case pat of
  --                    _ -> typeOf pat)
  --              | ListCompArm pat _ <- lcs ]
  --   compileDistVarPatt (CompiledTuplePat (map fst pats) (TupleType (map snd pats)))

zipTypes :: Type -> Type -> Compile Type
zipTypes t1 t2
  | Just e1 <- matchListType t1
  , Just e2 <- matchListType t2
  = return (mkListType (TupleType [e1, e2]))
zipTypes _ _ = error "Trying to zip a non-list!"

instance Compilable (GenExp Typed) TH.Exp where
  compile ge = withCompileCtx ge $ compile' ge where
    compile' (VarGenExp nm tp) = do
      let nm_th = (TH.AppE (TH.VarE 'allowUnused) (TH.VarE nm))
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE nm_th tp_th)
    compile' (BoundVarGenExp nm tp) =
      let nm' = compileIdent nm
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
      ee_th <-  lift $ lift [| SourceData (enumFromToByF $(bgE) $(toE) $(stE)) |]
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE ee_th tp_th)
    compile' (RangeGenExp bg Nothing st tp) = do
      let Just elm = matchListType tp
      elem_th <- compile elm
      let bgE = return (TH.SigE (TH.LitE (TH.IntegerL bg)) elem_th)
          stE = return (TH.LitE (TH.IntegerL st))
      ee_th <- lift $ lift [| SourceData (enumFromByF $(bgE) $(stE)) |]
      tp_th <- TH.AppT (TH.ConT ''Source) <$> compile tp
      return (TH.SigE ee_th tp_th)

instance Compilable (SourceExp Typed) TH.Exp where
  compile sexp = withCompileCtx sexp $ compile' sexp where
    compile' :: SourceExp Typed -> Compile TH.Exp
    compile' (VarSrcExp nm tp) =
      -- "Global" variables should always have type Source a, as they should
      -- only be referring to defined source expressions
      TH.SigE (TH.VarE nm) <$> TH.AppT (TH.ConT ''Source) <$> compile tp
    compile' (BoundVarSrcExp nm tp) =
      -- Bound variables always have type GrappaData a, so apply SourceData
      let nm' = compileIdent nm in
      TH.SigE (applyTHExp (TH.ConE 'SourceData) [TH.VarE nm']) <$>
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
            let rTyp = typeOf rExp
            typ   <- zipTypes lTyp rTyp
            typTH <- TH.AppT (TH.ConT ''Source) <$> compile typ
            let innerFun = applyTHExp (TH.ConE 'SourceBind)
                  [ TH.LamE [TH.VarP rName]
                    (TH.AppE (TH.ConE 'SourceData)
                       (applyTHExp (TH.VarE 'zipGData)
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
        let aTyp = typeOf aExp
        foldM zip_srcs (aExpr, aTyp) as
      tp_th <- compile tp
      let src_tp = TH.AppT (TH.ConT ''Source) tp_th
      return $ flip TH.SigE src_tp $ applyTHExp (TH.ConE 'SourceBind)
        [ applyTHExp (TH.VarE 'mapSource)
            [ TH.LamE [map_pat] expr_th ]
        , fst zipped_th
        ]

instance Compilable (GPriorStmt Typed) TH.Exp where
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

-- We compile v-expressions into expresssions that build them and patterns that
-- destruct them. For v-expressions that are "generated", which includes
-- wildcards and lifted expression, we need to generate them in a statement
-- context, by calling interp__'vwild or interp__'vlift, respectively, so we
-- here just generate fresh TH variables and return a list of those variables as
-- well as the interp method needed to generate them, which should have type
--
-- (GVExpr repr a -> GStmt repr b) -> GStmt repr b
instance Compilable (VExp Typed) ((TH.Exp, TH.Exp -> TH.Exp),
                                  [(TH.Name, TH.Exp)]) where
  compile ve = withCompileCtx ve $ runWriterT $ go ve where
    go :: VExp Typed ->
          WriterT [(TH.Name, TH.Exp)] Compile (TH.Exp, TH.Exp -> TH.Exp)
    go (VarVExp n True _) = do
      let expr = TH.VarE $ compileVIdent n
          pat = TH.VarP $ compileIdent n
      return (expr, TH.LamE [pat])
    go (VarVExp n False _) = do
      let n_th = compileVIdent n
          expr = TH.VarE n_th
          pat = TH.VarP $ compileIdent n
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
    go (CtorVExp _ _ _) =
      error "FIXME HERE: cannot yet compile constructor v-expressions"


-- | Compile the pattern for the current model sub-case to a TH expression,
-- whose value is the return value for the current sub-case
compileReturnValue :: Compile TH.Exp
compileReturnValue = getModelSubCasePattern >>= helper where
  helper :: Pattern Typed -> Compile TH.Exp
  helper (VarPat x _) = return $ TH.VarE $ compileIdent x
  helper (WildPat _) =
    error "Unexpected wildcard pattern in model subcase!"
  helper (CtorPat ctor patts _) =
    do adt_th <- mkADTCtorTHExpInterp ctor <$> mapM helper patts
       embedM [| interp__'injADT $(return adt_th) |]
  helper (TuplePat patts _) =
    do tuple_th <- mkTupleBodyTHExp <$> mapM helper patts
       embedM [| interp__'injTuple $(return tuple_th) |]
  helper (LitPat (IntegerLit i) _) = return $ TH.LitE $ TH.IntegerL i
  helper (LitPat (RationalLit r) _) = return $ TH.LitE $ TH.RationalL r
  helper (SigPat patt _) = helper patt

instance Compilable (Stmt Typed) TH.Exp where
  compile stmt = withCompileCtx stmt $ go stmt where
    go ReturnStmt = do
      rs <- compileReturnValue
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
      let lhs_th = TH.VarP $ compileIdent x
      rhs_th <- compile rhs
      body_th <- compile body
      return $ TH.LetE [TH.ValD lhs_th (TH.NormalB rhs_th) []] body_th
    go (CaseStmt _e _cs) =
      error "FIXME HERE: case statements not (yet?) supported"


instance Compilable (Decl Typed) [TH.Dec] where
  compile d@(FunDecl nm annot fun_cases) =
    withLocalCompileEnv $ withCompileCtx d $ withCurrentFunction nm $
    do let nm_th = TH.mkName $ T.unpack $ interpIdent nm
       tp_th <- compile annot
       addResolvedGName nm $ ResGName { gname_ident = nm,
                                        gname_th_name = nm_th,
                                        gname_raw_th_name = Nothing,
                                        gname_type = annot,
                                        gname_fixity = TH.defaultFixity }
       Just fix_th <- compile_fix_parameter <$> get
       body_th <- compileFunExp fun_cases
       let body_fix_th =
             TH.AppE (TH.VarE 'interp__'fix)
             (TH.LamE [TH.VarP fix_th] body_th)
       return [ TH.SigD nm_th tp_th
              , TH.FunD nm_th [TH.Clause [] (TH.NormalB body_fix_th) []]
              ]

  compile (SourceDecl name _ src_exp) =
    do src_exp_th <- compile src_exp
       return [ TH.ValD (TH.VarP $ compileIdent name)
                (TH.NormalB src_exp_th) [] ]

  compile (MainDecl (GPriorStmt src_expr model_expr)
            (InfMethod { infName = meth , infParams = params })) =
    do model_th <- compile model_expr
       src_expr_th <- compile src_expr
       params_th <- mapM rawCompileExpr params
       let mainExpr =
             applyTHExp (TH.VarE (imRunFunc meth)) $
             params_th ++ src_expr_th : replicate (imModelCopies meth) model_th
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
  compile checked_e

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
          compile checked_d

grappa :: TH.QuasiQuoter
grappa =
  TH.QuasiQuoter
  { TH.quoteExp = \_ -> error "No Grappa quasi-quoter for expressions",
    TH.quotePat = \_ -> error "No Grappa quasi-quoter for patterns",
    TH.quoteType = \_ -> error "No Grappa quasi-quoter for types",
    TH.quoteDec = compileGrappa }
