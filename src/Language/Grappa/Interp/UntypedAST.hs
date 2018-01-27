{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Grappa.Interp.UntypedAST
  ( ppAsPython
  , UntypedRepr
  , fromUntypedRepr
  , fromUntypedModel
  , printAST
  , showAST
  , ToPythonDistVar
  ) where

import           Control.Monad.State
import           Data.Text (Text)
import qualified Data.Text as T

import           Language.Grappa.Interp
import           Language.Grappa.GrappaInternals
import           Language.Grappa.Frontend.DataSource

import           Text.PrettyPrint.ANSI.Leijen ((<+>), (<$$>), (<>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

--
-- * The Identity Representation
--

data UntypedRepr

fromUntypedRepr :: GExpr UntypedRepr a -> GExprRepr UntypedRepr a
fromUntypedRepr = unGExpr

fromUntypedModel :: GStmt UntypedRepr a -> GStmtRepr UntypedRepr a
fromUntypedModel = unGStmt

showAST :: S UntypedAST -> String
showAST mote =
  let letters = map T.singleton ['a'..'z']
      vrs =
        letters ++ [ T.append a b
                   | a <- letters
                   , b <- vrs
                   ]
      vrs' = map (T.cons '_') vrs
      doc = ppUntypedAST (fst (runState mote (SState vrs' [])))
  in PP.displayS (PP.renderPretty 0.5 80 doc) ""

printAST :: S UntypedAST -> IO ()
printAST mote =
  let letters = map T.singleton ['a'..'z']
      vrs =
        letters ++ [ T.append a b
                   | a <- letters
                   , b <- vrs
                   ]
      vrs' = map (T.cons '_') vrs
      doc = ppAsPython (fst (runState mote (SState vrs' [])))
  in PP.putDoc doc

data SState = SState
  { ssVars  :: [Text]
  , ssFresh :: [Text]
  }

type S = State SState

getVar :: S Text
getVar = do
  s@SState { ssVars = x:xs, ssFresh = fs } <- get
  put s { ssVars = xs
        , ssFresh = x : fs
        }
  return x

clearFresh :: S ()
clearFresh = do
  modify $ \ s -> s { ssFresh = [] }

getFresh :: S [Text]
getFresh = do
  s@SState { ssFresh = fs } <- get
  put s { ssFresh = [] }
  return (reverse fs)


data UntypedAST
  = Var Text
  | Op Text
  | IntLit Integer
  | DoubleLit Double
  | App UntypedAST UntypedAST
  | Wild
  | Return UntypedAST
  | Sample UntypedAST UntypedAST UntypedAST
  | DistOf Text UntypedAST
  | LamOf UntypedPat UntypedAST
  | Tuple [UntypedAST]
  | ProjTuple [Text] UntypedAST UntypedAST
  | IfThenElse UntypedAST UntypedAST UntypedAST
  | Fix Text UntypedAST
  | DistNormal
  | DistUniform
  | ListLiteral [UntypedAST]
  | Let Text UntypedAST UntypedAST
    deriving (Show)

data UntypedPat
  = PatVar Text
  | PatTup [Text]
    deriving (Show)

isTypicalCall :: UntypedAST -> Maybe (UntypedAST, [UntypedAST])
isTypicalCall (App x y)
  | Just (f, xs) <- isTypicalCall x
  = Just (f, xs ++ [y])
isTypicalCall (App f x) = Just (f, [x])
isTypicalCall _ = Nothing

header :: String
header = "from grappa import *\n"

footer :: String
footer = unlines
  [ "def main():"
  , "    return model(src)"
  ]

ppAsPython :: UntypedAST -> PP.Doc
ppAsPython ast =
  PP.text header <$$> go ast <$$> PP.text footer
  where go (Sample (Fix n body) src _) =
          PP.text (T.unpack n) <+> PP.text "=" <+>
          PP.parens (PP.nest 2 (ppUntypedAST body)) <$$>
          PP.text "model" <+> PP.text "=" <+> PP.text (T.unpack n) <$$>
          PP.text "src" <+> PP.text "=" <+> ppUntypedAST src
        go (Sample dist src _)
          | Just (Fix n body, xs) <- isTypicalCall dist
          = PP.text (T.unpack n) <+> PP.text "=" <+>
            PP.parens (PP.nest 2 (ppUntypedAST body)) <$$>
            PP.text "model" <+> PP.text "=" <+> PP.text (T.unpack n) <>
            mconcat [ PP.parens (ppUntypedAST x) | x <- xs ] <$$>
            PP.text "src" <+> PP.text "=" <+> ppUntypedAST src
        go rs = error (show rs)

ppUntypedAST :: UntypedAST -> PP.Doc
ppUntypedAST (Var t) = PP.text (T.unpack t)
ppUntypedAST (Op t) = PP.parens (PP.text (T.unpack t))
ppUntypedAST (IntLit i) = PP.text (show i)
ppUntypedAST (DoubleLit i) = PP.text (show i)
ppUntypedAST (App x y)
  | App f z <- x
  , Op op <- f
  = PP.parens (ppUntypedAST z <+> PP.text (T.unpack op) <+> ppUntypedAST y)
  | Just (f, xs) <- isTypicalCall (App x y)
  = ppUntypedAST f <> mconcat [ PP.parens (ppUntypedAST a) | a <- xs ]
  | otherwise
  = PP.parens (ppUntypedAST x) <> PP.parens (ppUntypedAST y)
ppUntypedAST Wild = PP.text "_"
ppUntypedAST (Return e) = ppUntypedAST e
ppUntypedAST (Sample d dv e) =
  PP.text "sample" <>
  PP.parens (ppUntypedAST dv <> PP.text "," <+>
             ppUntypedAST d <> PP.text "," <+>
             ppUntypedAST e)
ppUntypedAST (DistOf t e) =
  PP.text "lambda" <+> PP.text (T.unpack t) <> PP.text ":" <+>
  PP.nest 2 (ppUntypedAST e)
ppUntypedAST (LamOf t e) =
  PP.text "lambda" <+> ppUntypedPat t <> PP.text ":" <+>
  PP.nest 2 (ppUntypedAST e)
ppUntypedAST (Tuple ts) =
  PP.parens (PP.hsep (PP.punctuate (PP.text ",") (map ppUntypedAST ts)))
ppUntypedAST (ListLiteral ts) =
  PP.brackets (PP.hsep (PP.punctuate (PP.text ",") (map ppUntypedAST ts)))
ppUntypedAST (ProjTuple ts t e) =
  ppUntypedAST (App (App (App (Var "proj") t)
                     (IntLit (fromIntegral (length ts))))
                 (LamOf (PatTup ts) e))
ppUntypedAST (IfThenElse c t e) =
  PP.parens (ppUntypedAST t) <+>
  PP.text "if" <+> PP.parens (ppUntypedAST c) <+>
  PP.text "else" <+> PP.parens (ppUntypedAST e)
ppUntypedAST (Fix n e) =
  ppUntypedAST (App (Var "fixpoint") (LamOf (PatVar n) e))
ppUntypedAST DistNormal = PP.text "normal_repr"
ppUntypedAST DistUniform = PP.text "uniform_repr"
ppUntypedAST (Let v e rs) =
  PP.parens (PP.text "lambda" <+> PP.text (T.unpack v) <+> ppUntypedAST rs) <>
  PP.parens (ppUntypedAST e)

ppUntypedPat :: UntypedPat -> PP.Doc
ppUntypedPat (PatVar v) =
  PP.text (T.unpack v)
ppUntypedPat (PatTup []) = PP.text "_"
ppUntypedPat (PatTup ts) =
  PP.parens (PP.hsep (PP.punctuate (PP.text ",") (map (PP.text . T.unpack) ts)))

instance ValidExprRepr (UntypedRepr) where
  type GExprRepr  UntypedRepr a = S UntypedAST

  interp__'bottom = error "UntypedRepr: unexpected bottom!"

  interp__'injTuple Tuple0 =
    GExpr $ Tuple <$> sequence []
  interp__'injTuple (Tuple1 (GExpr a)) =
    GExpr $ Tuple <$> sequence [a]
  interp__'injTuple (Tuple2 (GExpr a) (GExpr b)) =
    GExpr $ Tuple <$> sequence [a, b]
  interp__'injTuple (Tuple3 (GExpr a) (GExpr b) (GExpr c)) =
    GExpr $ Tuple <$> sequence [a, b, c]
  interp__'injTuple (Tuple4 (GExpr a) (GExpr b) (GExpr c) (GExpr d)) =
    GExpr $ Tuple <$> sequence [a, b, c, d]
  interp__'injTuple (TupleN (GExpr a) (GExpr b) (GExpr c) (GExpr d) (GExpr e) _) =
    GExpr $ Tuple <$> sequence [a, b, c, d, e]

  interp__'projTuple (GExpr tup) k = GExpr $ do
    tup' <- tup
    clearFresh
    vars <- traverseADT (\ _ -> do v <- getVar
                                   return (GExpr (return (Var v))))
              typeListProxy
    bs <- getFresh
    body <- unGExpr (k vars)
    return (ProjTuple bs tup' body)

  interp__'app (GExpr f) (GExpr x) =
    GExpr (App <$> f <*> x)
  interp__'lam f = GExpr $ do
    v <- getVar
    b <- unGExpr $ f $ GExpr (return $ Var v)
    return (LamOf (PatVar v) b)

  interp__'fix f = GExpr $ do
    self <- getVar
    body <- unGExpr (f (GExpr (return (Var self))))
    return (Fix self body)


instance ValidRepr (UntypedRepr) where
  type GVExprRepr UntypedRepr a = S UntypedAST
  type GStmtRepr  UntypedRepr a = S UntypedAST

  interp__'projTupleStmt (GExpr tup) k = GStmt $ do
    tup' <- tup
    clearFresh
    vars <- traverseADT (\ _ -> do v <- getVar
                                   return (GExpr (return (Var v))))
              typeListProxy
    bs <- getFresh
    body <- unGStmt (k vars)
    return (ProjTuple bs tup' body)

  interp__'vProjTuple (GVExpr tup) k = GStmt $ do
    tup' <- tup
    clearFresh
    vars <- traverseADT (\ _ -> do v <- getVar
                                   return (GVExpr (return (Var v))))
              typeListProxy
    bs <- getFresh
    body <- unGStmt (k vars)
    return (ProjTuple bs tup' body)

  interp__'vInjTuple Tuple0 =
    GVExpr $ Tuple <$> sequence []
  interp__'vInjTuple (Tuple1 (GVExpr a)) =
    GVExpr $ Tuple <$> sequence [a]
  interp__'vInjTuple (Tuple2 (GVExpr a) (GVExpr b)) =
    GVExpr $ Tuple <$> sequence [a, b]
  interp__'vInjTuple (Tuple3 (GVExpr a) (GVExpr b) (GVExpr c)) =
    GVExpr $ Tuple <$> sequence [a, b, c]
  interp__'vInjTuple (Tuple4 (GVExpr a) (GVExpr b) (GVExpr c) (GVExpr d)) =
    GVExpr $ Tuple <$> sequence [a, b, c, d]
  interp__'vInjTuple (TupleN (GVExpr a) (GVExpr b) (GVExpr c) (GVExpr d) (GVExpr e) _) =
    GVExpr $ Tuple <$> sequence [a, b, c, d, e]

  interp__'vwild k =
    k $ GVExpr (return Wild)

  interp__'vlift _ = undefined

  interp__'return (GExpr x) =
    GStmt (Return <$> x)
  interp__'let (GExpr rhs) k = GStmt $ do
    v <- getVar
    rhs' <- rhs
    body <- unGStmt $ k (GExpr (return (Var v)))
    return (Let v rhs' body)

  interp__'sample (GExpr d) (GVExpr dv) k = GStmt $ do
    v <- getVar
    d' <- d
    dv' <- dv
    body <- unGStmt $ k (GExpr (return (Var v)))
    return (Sample d' dv' (LamOf (PatVar v) body))

  interp__'mkDist f = GExpr $ do
    v <- getVar
    s <- unGStmt $ f $ GVExpr (return $ Var v)
    return (DistOf v s)

instance Interp__'ifThenElse UntypedRepr where
  interp__'ifThenElse (GExpr c) (GExpr t) (GExpr e) =
    GExpr (IfThenElse <$> c <*> t <*> e)

instance Num a => Interp__'plus UntypedRepr a where
  interp__'plus = GExpr $ return (Op "+")

instance Num a => Interp__'minus UntypedRepr a where
  interp__'minus = GExpr $ return (Op "-")

instance (Num a) => Interp__'times UntypedRepr a where
  interp__'times = GExpr $ return (Op "*")

instance Num a => Interp__negate UntypedRepr a where
  interp__negate = GExpr $ return (Op "-")

instance Num a => Interp__abs UntypedRepr a where
  interp__abs = GExpr $ return (Var "abs")

instance Num a => Interp__signum UntypedRepr a where
  interp__signum = GExpr $ return (Var "signum")

instance Fractional a => Interp__'div UntypedRepr a where
  interp__'div = GExpr $ return (Op "/")

instance Floating a => Interp__'times'times UntypedRepr a where
  interp__'times'times = GExpr $ return (Op "**")

instance Num a => Interp__fromInteger UntypedRepr a where
  interp__fromInteger = GExpr $ return (Var "fromInteger")

instance (Num a) => Interp__'integer UntypedRepr a where
  interp__'integer  n =
    GExpr $ return (IntLit n)

instance (Fractional a) => Interp__'rational UntypedRepr a where
  interp__'rational  n =
    GExpr $ return (DoubleLit (fromRational n))

instance (Num a) => Interp__'eqInteger UntypedRepr a where
  interp__'eqInteger (GExpr x) (GExpr y) = GExpr $ do
    x' <- x
    y' <- y
    return (Op "==" `App` x' `App` y')

instance Interp__normal UntypedRepr where
  interp__normal = GExpr (return DistNormal)

instance Interp__ctorDist__ListF UntypedRepr where
  interp__ctorDist__Nil = GExpr $ return (Var "list_repr.nil_dist")
  interp__ctorDist__Cons = GExpr $ return (Var "list_repr.cons_dist")

instance ToPythonDistVar r => Interp__'source UntypedRepr r where
  interp__'source src = do
    dv <- interpSource src
    return (GVExpr (return (toPythonDistVar dv)))

class ToPythonDistVar t where
  toPythonDistVar :: GrappaData t -> UntypedAST

instance ToPythonDistVar Double where
  toPythonDistVar GNoData = (Var "None")
  toPythonDistVar (GData n) = (DoubleLit n)

instance ToPythonDistVar Int where
  toPythonDistVar GNoData = (Var "None")
  toPythonDistVar (GData n) = (IntLit (fromIntegral n))

instance forall t. ToPythonDistVar t => ToPythonDistVar (GList t) where
  toPythonDistVar = toPythonDistVarH . matchADTGDataMaybe
    where
      toPythonDistVarH Nothing = (Var "None")
      toPythonDistVarH (Just list) = case gather list of
        Just lst -> App (Var "grappa_list") (ListLiteral lst)
        Nothing -> case list of
          Cons x xs ->
            App (Var "list_repr.Cons")
            (Tuple [ toPythonDistVar x
                   , toPythonDistVar xs
                   ])
          Nil -> App (Var "list_repr.Nil") (Tuple [])
      gather :: ToPythonDistVar t => ListF t GrappaData (ADT (ListF t)) ->
                Maybe [UntypedAST]
      gather (Cons x (matchADTGDataMaybe -> Just xs)) = do
        rs <- gather xs
        return (toPythonDistVar x : rs)
      gather (Cons _ _) = Nothing
      gather Nil = Just []

instance MapC ToPythonDistVar ts => ToPythonDistVar (GTuple ts) where
  toPythonDistVar = toPythonDistVarH . matchADTGDataMaybe
    where
      toPythonDistVarH Nothing = (Var "None")
      toPythonDistVarH (Just tup) = Tuple (tupleToPython tup)

tupleToPython :: MapC ToPythonDistVar ts => TupleF ts GrappaData r ->
                 [UntypedAST]
tupleToPython Tuple0 = []
tupleToPython (Tuple1 a) = [ toPythonDistVar a ]
tupleToPython (Tuple2 a b) =
  [ toPythonDistVar a
  , toPythonDistVar b
  ]
tupleToPython (Tuple3 a b c) =
  [ toPythonDistVar a
  , toPythonDistVar b
  , toPythonDistVar c
  ]
tupleToPython (Tuple4 a b c d) =
  [ toPythonDistVar a
  , toPythonDistVar b
  , toPythonDistVar c
  , toPythonDistVar d
  ]
tupleToPython (TupleN a b c d e rs) =
  ( toPythonDistVar a
  : toPythonDistVar b
  : toPythonDistVar c
  : toPythonDistVar d
  : toPythonDistVar e
  : tupleToPython rs
  )


instance Interp__uniform UntypedRepr where
  interp__uniform = GExpr (return DistUniform)
