{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- | Functions that ease interoperability between template-haskell versions
module Language.Haskell.TH.Compat where

import Language.Haskell.TH (reify, Kind, Name, Type(..))
import qualified Language.Haskell.TH as TH

-- | Almost certainly doesn't do what you want for 'ForallT'. Make sure you
-- handle at least that one yourself!
fmapType :: (Name -> Name) -> (Type -> Type) -> (Kind -> Kind) -> (Type -> Type)
fmapType fNm fTy fK ty_ = case ty_ of
  ForallT tyvars ctx ty -> ForallT tyvars ctx (fTy ty)
  AppT ty ty' -> AppT (fTy ty) (fTy ty')
  SigT ty k -> SigT (fTy ty) (fK k)
  VarT nm -> VarT (fNm nm)
  ConT nm -> ConT (fNm nm)
  PromotedT nm -> PromotedT (fNm nm)
#if MIN_VERSION_template_haskell(2,11,0)
  InfixT ty nm ty' -> InfixT (fTy ty) (fNm nm) (fTy ty')
  UInfixT ty nm ty' -> UInfixT (fTy ty) (fNm nm) (fTy ty')
  ParensT ty -> ParensT (fTy ty)
#endif
  ty -> ty

#if MIN_VERSION_template_haskell(2,11,0)
pattern DataD :: TH.Cxt -> Name -> [TH.TyVarBndr] -> [TH.Con] -> TH.Dec
pattern DataD    ctx nm tyvars cons <- TH.DataD    ctx nm tyvars _ cons _

pattern NewtypeD :: TH.Cxt -> Name -> [TH.TyVarBndr] -> TH.Con -> TH.Dec
pattern NewtypeD ctx nm tyvars con <- TH.NewtypeD ctx nm tyvars _ con _

#else
pattern DataD    ctx nm tyvars cons <- TH.DataD    ctx nm tyvars   cons _
pattern NewtypeD ctx nm tyvars con <- TH.NewtypeD ctx nm tyvars   con _
#endif

#if MIN_VERSION_template_haskell(2,11,0)
dataD :: TH.Cxt -> Name -> [TH.TyVarBndr] -> [TH.Con] -> TH.Dec
dataD    ctx nm tyvars cons = TH.DataD    ctx nm tyvars Nothing cons []

newtypeD :: TH.Cxt -> Name -> [TH.TyVarBndr] -> TH.Con -> TH.Dec
newtypeD ctx nm tyvars con = TH.NewtypeD ctx nm tyvars Nothing con []
#else
dataD    ctx nm tyvars cons = TH.DataD    ctx nm tyvars cons []
newtypeD ctx nm tyvars con = TH.NewtypeD ctx nm tyvars con []
#endif

#if MIN_VERSION_template_haskell(2,11,0)
reifyFixity :: Name -> TH.Q (Maybe TH.Fixity)
reifyFixity = TH.reifyFixity
#else
reifyFixity nm = do
  info <- reify nm
  case info of
    TH.ClassOpI _ _ _ fixity -> return (Just fixity)
    TH.DataConI _ _ _ fixity -> return (Just fixity)
    TH.VarI     _ _ _ fixity -> return (Just fixity)
    _ -> return Nothing
#endif

#if MIN_VERSION_template_haskell(2,11,0)
pattern ClassOpI :: Name -> Type -> TH.ParentName -> TH.Info
pattern ClassOpI nm ty par <- TH.ClassOpI nm ty par

pattern DataConI :: Name -> Type -> TH.ParentName -> TH.Info
pattern DataConI nm ty par <- TH.DataConI nm ty par

pattern VarI :: Name -> Type -> Maybe TH.Dec -> TH.Info
pattern VarI     nm ty dec <- TH.VarI     nm ty dec
#else
pattern ClassOpI nm ty par <- TH.ClassOpI nm ty par _
pattern DataConI nm ty par <- TH.DataConI nm ty par _
pattern VarI     nm ty dec <- TH.VarI     nm ty dec _
#endif
