{-# LANGUAGE GADTs, TemplateHaskell #-}

module Language.Haskell.TH.GrappaUtil where

import Data.Functor.Const

import Language.Grappa.GrappaInternals
import Language.Grappa.Frontend.AST
import Language.Grappa.Interp

import qualified Language.Haskell.TH as TH


--
-- * Helper Functions for Building Template Haskell for Grappa Expressions
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
mkLamInterp pats body = foldr go body pats
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


-- | Typeclass for ADTs that we know how to convert into TH
--
-- FIXME: unify the below with some of the stuff above!
class TraversableADT adt => THADT adt where
  -- | Get the TH name for the constructor of an adt object
  adtHeadCtorName :: adt f r -> TH.Name

-- | Typed wrapper around a TH name
newtype THName a = THName { getTHName :: TH.Name }

-- | Create a fresh 'THName'
newTHName :: String -> TH.Q (THName a)
newTHName str = THName <$> TH.newName str

-- | Convert a constructor application to TH exprs into a TH expression
adtToTHExp :: THADT adt => adt (Const TH.Exp) (ADT adt) -> TH.Exp
adtToTHExp adt =
  applyTHExp (TH.ConE $ adtHeadCtorName adt) (ctorArgsADT getConst adt)

-- | Convert a constructor application to TH names into a TH pattern
adtToTHPattern :: THADT adt => adt THName (ADT adt) -> TH.Pat
adtToTHPattern adt =
  TH.ConP (adtHeadCtorName adt) (ctorArgsADT (TH.VarP . getTHName) adt)

instance THADT (TupleF ts) where
  adtHeadCtorName Tuple0 = 'Tuple0
  adtHeadCtorName (Tuple1 {}) = 'Tuple1
  adtHeadCtorName (Tuple2 {}) = 'Tuple2
  adtHeadCtorName (Tuple3 {}) = 'Tuple3
  adtHeadCtorName (Tuple4 {}) = 'Tuple4
  adtHeadCtorName (TupleN {}) = 'TupleN

instance THADT (ListF a) where
  adtHeadCtorName Nil = 'Nil
  adtHeadCtorName (Cons {}) = 'Cons
