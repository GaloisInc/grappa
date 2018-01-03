{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ParallelListComp #-}

module Language.Grappa.Frontend.Matching where

import Control.Monad.Except
import Control.Monad.State

import Data.List (findIndex, transpose)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Data.Text as T

import qualified Language.Haskell.TH as TH

import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.TypeCheck

data PatternMatchError
  = ErrorWildCardInVExpr
  | OverlappingCases
  | WildCardInCtorPattern
    deriving Show

data MatchEnv = MatchEnv
  { meExpMap  :: Map Int (Exp Typed)
  , meVExpMap :: Map Int (VExp Typed)
  , meLastVar :: Int
  } deriving Show


emptyMatchEnv :: MatchEnv
emptyMatchEnv = MatchEnv
  { meExpMap  = Map.empty
  , meVExpMap = Map.empty
  , meLastVar = 0
  }

type MatchM = StateT MatchEnv (ExceptT PatternMatchError TH.Q)

instance SubMonad TH.Q MatchM where
  embedM m = lift (lift m)

-- | A value of type 'CompileMatch'' represents a strategy for
-- compiling certain cases in our AST. It has four type variables:
--
-- - The type of the scrutinee of the match
--
-- - The type of an individual case of the pattern-match
--
-- - The type of the body of a case, which we'll need to recurse into
--   when we're done processing the current cases
--
-- - The type of the resulting overall expression, which might not be
--   the same thing we started with (e.g. we compile top-level model
--   declarations to top-level functions that return an anonymous
--   model.)
data CompileMatch' scrut case' leftover result = CompileMatch'
  { cmGetBinding     :: Int -> MatchM scrut
    -- ^ Get a generated binding by its index
  , cmMkCase         :: Type -> Pattern Rewritten -> result -> MatchM case'
    -- ^ Given a type, a pattern, and a body for that pattern, create
    -- a datatype representing that single case.
  , cmCompileRest    :: leftover -> MatchM result
    -- ^ Traverse down into the body of a pattern-match, if any, and
    -- rewrite the patterns there.
  , cmMkStmt         :: scrut -> [case'] -> MatchM result
    -- ^ Given a scrutinee and several cases, produce the resulting
    -- AST node
  , cmRename         :: Ident -> Exp Typed -> VExp Typed -> leftover -> leftover
    -- ^ Perform a renaming inside of the as-yet unrewritten body
  , cmAllowWildcards :: Bool
    -- ^ Whether to allow wildcards in a match (should be true for
    -- expressions, false for models)
  }

type CompileMatch s c l r =
  CompileMatch' (s Rewritten) (c Rewritten) (l Typed) (r Rewritten)

compileTopLevelMatch ::
  CompileMatch' (Exp Rewritten)
                (ExpCase Rewritten)
                [ModelSubCase Typed]
                (Exp Rewritten)
compileTopLevelMatch = CompileMatch' { .. }
  where cmGetBinding n = getNthVar n >>= rewriteMatches
        cmMkCase t pat r = return (ExpCase pat r t (getTypeOf r))
        cmCompileRest = rewriteSubcaseMatches
        cmMkStmt scrut cs =
          return (CaseExp scrut cs (getTypeOf (head cs)))
        cmRename  i e _ l =
          renameVar i e l
        cmAllowWildcards = True

compileExprMatch :: CompileMatch Exp ExpCase Exp Exp
compileExprMatch = CompileMatch' { .. }
  where
    cmGetBinding n = getNthVar n >>= rewriteMatches
    cmMkCase t pat r = return (ExpCase pat r t (getTypeOf r))
    cmCompileRest  l = rewriteMatches l
    cmMkStmt scrut cs =
      return (CaseExp scrut cs (getTypeOf (head cs)))
    cmRename i e _ l = renameVar i e l
    cmAllowWildcards = True

compileVExprMatch :: CompileMatch VExp ModelSubCase Stmt Stmt
compileVExprMatch = CompileMatch' { .. }
  where
    cmGetBinding n = getNthVExp n >>= rewriteMatches
    cmMkCase _ pat r =  return (ModelSubCase pat Nothing r)
    cmCompileRest s = rewriteMatches s
    cmMkStmt scrut cs =
      return (SampleStmt scrut (ModelExp cs (getTypeOf (head cs))) ReturnStmt)
    cmRename i e v l =
      fullyRenameVExpr i e v l
    cmAllowWildcards = False

compileStmtMatch :: CompileMatch Exp StmtCase Stmt Stmt
compileStmtMatch = CompileMatch' { .. }
  where
    cmGetBinding n    = getNthVar n >>= rewriteMatches
    cmMkCase t pat r  = return (StmtCase pat r t)
    cmCompileRest s   = rewriteMatches s
    cmMkStmt scrut cs = return (CaseStmt scrut cs)
    cmRename i e _ l  = renameVar i e l
    cmAllowWildcards  = True

insertBinding :: Exp Typed -> MatchM Int
insertBinding e = do
  vars <- meExpMap <$> get
  lst <- meLastVar <$> get
  let n = lst + 1
  modify $ \ m -> m { meExpMap = Map.insert n e vars
                    , meLastVar = n
                    }
  return n

newBinding :: Type -> MatchM (CompiledVarPattern Rewritten, Int)
newBinding t = do
  vars <- meExpMap <$> get
  lst <- meLastVar <$> get
  ident <- fmap (T.pack . show) $ embedM $ TH.newName "_i"
  let n = lst + 1
      expr = NameExp (LocalName ident) t
      p    = VarCPat ident t
  modify $ \ m -> m { meExpMap = Map.insert n expr vars
                    , meLastVar = n
                    }
  return (p, n)

newVBinding :: Type -> MatchM (CompiledVarPattern Rewritten, Int)
newVBinding t = do
  exprs  <- meExpMap <$> get
  vExprs <- meVExpMap <$> get
  lst    <- meLastVar <$> get
  ident  <- fmap (T.pack . show) $ embedM $ TH.newName "_v"
  let n = lst + 1
      expr  = NameExp (LocalName ident) t
      vExpr = VarVExp ident True t
      p     = VarCPat ident t
  modify $ \ m -> m { meVExpMap = Map.insert n vExpr vExprs
                    , meExpMap  = Map.insert n expr exprs
                    , meLastVar = n
                    }
  return (p, n)

getNthVar :: Int -> MatchM (Exp Typed)
getNthVar n = do
  mp <- meExpMap `fmap` get
  return (mp Map.! n)

getNthVExp :: Int -> MatchM (VExp Typed)
getNthVExp n = do
  mp <- meVExpMap `fmap` get
  return (mp Map.! n)

-- | Get an 'arbitrary' element of a map
getOne :: Map k v -> v
getOne = head . Map.elems

-- | Each branch is a set of patterns with something at the end: it
-- might be ModelSubCase (for top-level things) or just expressions
-- (for other match rewritings)
type Branch r = ([WrappedPattern], r)
type MatchedBranch r = (WrappedPattern, Branch r)
data PatternGroups r
  = PGVars [MatchedBranch r]
  | PGLits (Map Literal [MatchedBranch r]) [MatchedBranch r]
  | PGCtors (Map (Maybe (CtorName Typed)) [MatchedBranch r]) [MatchedBranch r]

-- | A WrappedPattern is a pattern along with an 'index'; each pattern
-- comes from one or more
data WrappedPattern = WrappedPattern
  { wpIdx :: Int
  , wpPat :: Pattern Typed
  } deriving (Show)

-- | Split the list into the elements before the Nth, the Nth, and the
-- elements after the Nth.
partitionNth :: Int -> [a] -> ([a], a, [a])
partitionNth 0 (x:xs) = ([], x, xs)
partitionNth 0 []     = error "partitionNth: empty list"
partitionNth n (x:xs) =
  let (a, b, c) = partitionNth (n-1) xs
  in (x : a, b, c)
partitionNth _ [] = error "partitionNth: list too short"

-- | Count the number of distinct constructors/patterns in a given
-- pattern-match. We give precedence to matches that match a larger
-- number of cases.
countConstructors :: [WrappedPattern] -> Int
countConstructors = go 0 [] . map wpPat
  where
    go n _ [] = n
    go n s (VarPat {}:rs) = go n s rs
    go n s (WildPat {}:rs) = go n s rs
    go n s (SigPat p _:rs) = go n s (p:rs)
    go n s (CtorPat name _ _:rs)
      | Left name `elem` s = go n s rs
      | otherwise = go (n+1) (Left name:s) rs
    go n s (LitPat l _:rs)
      | Right l `elem` s = go n s rs
      | otherwise = go (n+1) (Right l:s) rs
    go n s (TuplePat ps _:rs) =
      go (go 0 [] ps + n) s rs


class RewriteMatches f where
  rewriteMatches :: f Typed -> MatchM (f Rewritten)

instance RewriteMatches Stmt where
  rewriteMatches ReturnStmt = return ReturnStmt
  rewriteMatches (SampleStmt v e s) =
    SampleStmt <$> rewriteMatches v <*> rewriteMatches e <*> rewriteMatches s
  rewriteMatches (LetStmt i e s) =
    LetStmt i <$> rewriteMatches e <*> rewriteMatches s
  rewriteMatches (CaseStmt e cs) = do
    num <- insertBinding e
    let branches = [ ([WrappedPattern num p], c)
                   | StmtCase p c _ <- cs
                   ]
    rewriteCases compileStmtMatch branches

instance RewriteMatches VExp where
  rewriteMatches (VarVExp v i tp) = return (VarVExp v i tp)
  rewriteMatches (WildVExp tp) = return (WildVExp tp)
  rewriteMatches (SigVExp vexp tp) =
    SigVExp <$> rewriteMatches vexp <*> return tp
  rewriteMatches (CtorVExp ctor vexps tp) =
    CtorVExp ctor <$> mapM rewriteMatches vexps <*> return tp
  rewriteMatches (TupleVExp vexps tp) =
    TupleVExp <$> mapM rewriteMatches vexps <*> return tp
  rewriteMatches (EmbedVExp expr tp) =
    EmbedVExp <$> rewriteMatches expr <*> return tp


instance RewriteMatches Exp where
  rewriteMatches = go
    where go (SigExp e t) =
            SigExp <$> go e <*> return t
          go (AppExp e es t) =
            AppExp <$> go e <*> mapM go es <*> return t
          go (TupleExp es t) =
            TupleExp <$> mapM go es <*> return t
          go (LetExp i t1 e1 e2 t2) =
            LetExp i t1 <$> go e1 <*> go e2 <*> return t2
          go (CaseExp e cs _) = do
            num <- insertBinding e
            let branches = [ ([WrappedPattern num p], c)
                           | ExpCase p c _ _ <- cs
                           ]
            rewriteCases compileExprMatch branches
          go (ModelExp cs t) = do
            let samplePat = head [ pat | ModelSubCase pat _ _ <- cs ]
            (b, num) <- newVBinding (patternType samplePat)
            let branches = [ ([WrappedPattern num p], c)
                           | ModelSubCase p _ c <- cs
                           ]
            rs <- rewriteCases compileVExprMatch branches
            return (ModelExp [ModelSubCase (CompiledBasicPattern b) Nothing rs] t)
          go (IfExp c t e tp) =
            IfExp <$> go c <*> go t <*> go e <*> return tp
          go (FunExp (FunCase ps e) tp) = do
            bs <- mapM (newBinding . patternType) ps
            let (bindings, nums) = unzip bs
                branches = (zipWith WrappedPattern nums ps, e)
            rest <- rewriteCases compileExprMatch [branches]
            return (FunExp (FunCase bindings rest) tp)
          go (NameExp n t) = NameExp <$> rewriteMatches n <*> return  t
          go (LiteralExp l t) = return (LiteralExp l t)
          go (OpExp enabled _ _ _) = notEnabled enabled
          go (ParensExp enabled _) = notEnabled enabled
          go (ListExp enabled _) = notEnabled enabled

instance RewriteMatches Name where
  rewriteMatches (LocalName i) = return $ LocalName i
  rewriteMatches (GlobalName i) = return $ GlobalName i
  rewriteMatches (CtorName i) = return $ CtorName i

-- models actually become functions that return anonymous models
instance RewriteMatches Decl where
  rewriteMatches (ModelDecl name typ modelCases@(ModelCase ps _:_)) = do
    bs <- mapM (newBinding . patternType) ps
    let (bindings, nums) = unzip bs
        branches = [ (zipWith WrappedPattern nums p, c)
                   | ModelCase p c <- modelCases
                   ]
    subcase <- rewriteCases compileTopLevelMatch branches
    return $ FunDecl name typ [FunCase bindings subcase]
  rewriteMatches (ModelDecl _ _ []) =
    error "Unreachable: model decl with no cases"
  rewriteMatches (FunDecl name typ funCases@(FunCase ps _:_)) = do
    bs <- mapM (newBinding . patternType) ps
    let (bindings, nums) = unzip bs
        branches = [ (zipWith WrappedPattern nums p, e)
                   | FunCase p e <- funCases
                   ]
    subcase <- rewriteCases compileExprMatch branches
    return $ FunDecl name typ [FunCase bindings subcase]
  rewriteMatches (FunDecl _ _ []) =
    error "Unreachable: fun decl with no cases"
  rewriteMatches (SourceDecl n t e) =
    SourceDecl n t <$> rewriteMatches e
  rewriteMatches (MainDecl gp m) =
    MainDecl <$> rewriteMatches gp <*> rewriteMatches m

instance RewriteMatches InfMethod where
  rewriteMatches (InfMethod name params) =
    InfMethod name <$> mapM rewriteMatches params

instance RewriteMatches GPriorStmt where
  rewriteMatches (GPriorStmt source expr) =
    GPriorStmt <$> rewriteMatches source <*> rewriteMatches expr

instance RewriteMatches SourceExp where
  rewriteMatches (VarSrcExp name typ) =
    return (VarSrcExp name typ)
  rewriteMatches (BoundVarSrcExp name typ) =
    return (BoundVarSrcExp name typ)
  rewriteMatches (WildSrcExp typ) =
    return (WildSrcExp typ)
  rewriteMatches (LiteralSrcExp lit typ) =
    return (LiteralSrcExp lit typ)
  rewriteMatches (CtorSrcExp ctor es typ) =
    CtorSrcExp ctor <$> mapM rewriteMatches es <*> return typ
  rewriteMatches (TupleSrcExp es typ) =
    TupleSrcExp <$> mapM rewriteMatches es <*> return typ
  rewriteMatches (FileSrcExp name ident typ) =
    return (FileSrcExp name ident typ)
  rewriteMatches (ListCompSrcExp e arms typ) =
    ListCompSrcExp <$> rewriteMatches e <*> mapM rewriteMatches arms <*> return typ

instance RewriteMatches ListCompArm where
  rewriteMatches _ = error "FIXME" -- XXX FIXME

-- subcases only have a single pattern, so those are easier to
-- rewrite
rewriteSubcaseMatches :: [ModelSubCase Typed] -> MatchM (Exp Rewritten)
rewriteSubcaseMatches modelSubCases@(ModelSubCase pat _ _:_) = do
  let typ = patternType pat
  (b, n) <- newVBinding typ
  let branches = [ ([WrappedPattern n p], s)
                 | ModelSubCase p _ s <- modelSubCases
                 ]
  stmt <- rewriteCases compileVExprMatch branches
  return $ ModelExp [ModelSubCase (CompiledBasicPattern b) Nothing stmt] (patternType pat)
rewriteSubcaseMatches [] =
  error "Empty subcase matches"

findNextMatch ::
  [[WrappedPattern]] ->
  MatchM [([WrappedPattern], WrappedPattern, [WrappedPattern])]
findNextMatch ps
  | all null ps = error "no patterns left"
  | all (\ l -> length l == 1) ps = return ( [ ([], p, []) | [p] <- ps ])
  | otherwise =
    let psT      = transpose ps
        mC       = maximum (map countConstructors psT)
        Just idx = findIndex (\ p -> countConstructors p == mC) psT
    in return (map (partitionNth idx) ps)

-- Gather like cases (i.e. cases made with like constructors) together
gatherCases :: [WrappedPattern] -> [Branch r] -> MatchM (PatternGroups r)
gatherCases pats exps =
     -- if all we have are variables/wild-cards, then they're all
     -- grouped together, because they are all handled by the same
     -- case
  if | null cs && null ls -> return $ PGVars vs
     -- if we have no constructor patterns, then group the like
     -- literals together
     | null cs -> return $ PGLits ls vs
     -- and contrariwise, if we have no literals, then group by
     -- constructors
     | null ls -> return $ PGCtors cs vs
       -- otherwise... what
     | otherwise -> error "Pattern-matching over both literals and constructors"
  where -- split patterns into constructor patterns, literals, and
          -- variable/wildcard patterns
        (cs, ls, vs) = splitPats pats exps
        -- split our patterns into (constructor, literal, variable)
        -- patterns; the former two are maps, indexed by the specific
        -- literal or constructor being matched on
        splitPats [] [] = (Map.empty, Map.empty, [])
        splitPats (p:ps) (e:es) =
          let (cons, lits, vars) = splitPats ps es
          in case wpPat p of
            VarPat {}   ->
              (cons, lits, (p, e):vars)
            WildPat {}  ->
              (cons, lits, (p, e):vars)
            CtorPat n _ _ ->
              (Map.insertWith (++) (Just n) [(p, e)] cons, lits, vars)
            TuplePat {} ->
              (Map.insertWith (++) Nothing [(p, e)] cons, lits, vars)
            LitPat n _ ->
              (cons, Map.insertWith (++) n [(p, e)] lits, vars)
            SigPat p' _ ->
              splitPats (p { wpPat = p' }:ps) (e:es)
        splitPats _ _ = error "[splitPats: unreachable]"

-- * The actual rewriting functions

-- So long as there are more patterns left
rewriteCases :: CompileMatch' c s l r -> [Branch l] -> MatchM r
rewriteCases match bs = do
  let pats = map fst bs
  if all null pats then
    case bs of
      [(_, rest)] -> cmCompileRest match rest
      []          -> error "unreachable"
      _           -> throwError OverlappingCases
    else do
      nextPats <- findNextMatch pats
      let (choice, bs') = unzip [ (next, (before ++ after, expr))
                                | (before, next, after) <- nextPats
                                | (_, expr) <- bs
                                ]
      groups <- gatherCases choice bs'
      compileGroup match groups

-- | Compile a group group of like patterns into a single pattern-match.
compileGroup :: CompileMatch' c s l r -> PatternGroups l -> MatchM r
-- We might have just variables, in which case we should just go
-- through and rewrite the right-hand sides to our new name for that
-- variable.
compileGroup match (PGVars vars) = do
  let (sPat, _):_ = vars
      idx  = wpIdx sPat
  expr  <- getNthVar idx
  vExpr <- getNthVExp idx
  let vars' = [ (ps, case wpPat p of
                       VarPat i _ ->
                         cmRename match i expr vExpr rs
                       WildPat _  -> rs
                       _ -> error "[unreachable]")
              | (p, (ps, rs)) <- vars
              ]
  rest <- rewriteCases match vars'
  return rest
-- We might have a pattern that includes literals, in which case we
-- should compile all the literals first, then compile the rest of
-- the patterns.
compileGroup match (PGLits lits vars) = do
  let sPat = fst (head (getOne lits))
      idx  = wpIdx sPat
      pTyp = patternType (wpPat sPat)
  cases <- mapM (uncurry (litCase match pTyp)) (Map.toList lits)
  finalCase <- case vars of
                 [] -> return []
                 _  -> do
                   fallthrough <- compileGroup match (PGVars vars)
                   let pat = CompiledBasicPattern (WildCPat pTyp)
                   c <- cmMkCase match pTyp pat fallthrough
                   return [c]
  expr <- cmGetBinding match idx
  cmMkStmt match expr (cases ++ finalCase)
-- And we might have a pattern that involves constructors.
compileGroup match (PGCtors ctors vars)
  | not (null vars) &&
    not (cmAllowWildcards match)
  = throwError WildCardInCtorPattern
  | otherwise = do
  let sPat = fst (head (getOne ctors))
      idx  = wpIdx sPat
      pTyp = patternType (wpPat sPat)
  cases <- mapM (uncurry (ctorCase match pTyp)) (Map.toList ctors)
  expr <- cmGetBinding match idx
  cmMkStmt match expr cases

litCase :: CompileMatch' s c l r -> Type -> Literal -> [MatchedBranch l] -> MatchM c
litCase match t lit bs = do
  rest <- rewriteCases match (map snd bs)
  cmMkCase match t (CompiledLitPat lit t) rest

ctorCase ::
  CompileMatch' s c l r ->
  Type ->
  Maybe (CtorName Typed) ->
  [MatchedBranch l] ->
  MatchM c
ctorCase match t (Just ctor) bs = do
  let nestedPats = [ pats | CtorPat _ pats _ <- map (wpPat . fst) bs ]
  bindings <- mapM (newVBinding . patternType) (head nestedPats)
  let otherCases = [ ( oldPats ++ zipWith WrappedPattern (map snd bindings) newPats
                     , subCase
                     )
                   | (_, (oldPats, subCase)) <- bs
                   | newPats <- nestedPats
                   ]
  rest <- rewriteCases match otherCases
  cmMkCase match t (CompiledCtorPat ctor (map fst bindings) t) rest
ctorCase match t Nothing bs = do
  let nestedPats = [ pats | TuplePat pats _ <- map (wpPat . fst) bs ]
  bindings <- mapM (newVBinding . patternType) (head nestedPats)
  let otherCases = [ ( oldPats ++ zipWith WrappedPattern (map snd bindings) newPats
                     , subCase
                     )
                   | (_, (oldPats, subCase)) <- bs
                   | newPats <- nestedPats
                   ]
  rest <- rewriteCases match otherCases
  cmMkCase match t (CompiledTuplePat (map fst bindings) t) rest

-- class GetPatterns t where
--   getPatterns :: t Typed -> RawPattern Typed

-- instance GetPatterns
