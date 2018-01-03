{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-all #-}

module Language.Grappa.Frontend.DataSource where

import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as BS
import qualified Data.Csv as Csv
import qualified Data.Foldable as F
import           Data.List (isPrefixOf)
import qualified Data.Vector as V
import           GHC.Exts (Constraint)
import qualified Numeric.AD.Mode as AD
import qualified Numeric.AD.Mode.Forward as AD

import           Language.Grappa.GrappaInternals


--
-- * DSL for Data Sources
--

data SourceFile format = SourceFile
  { sourceFile   :: FilePath
  , sourceFormat :: format
  } deriving (Show)

data Source a where
  -- | A fixed piece of data
  SourceData :: IsAtomic a ~ 'True => a -> Source a
  -- | A "parameter"
  SourceParam :: Source a
  -- | A constructor expression
  SourceCtor :: TraversableADT adt =>
                adt Source (ADT adt) -> Source (ADT adt)
  -- | A source file that represents a list-shaped data frame with 2 or more
  -- columns
  SourceReadFileRow ::
    (FromDataSource fmt rowC fieldC, rowC a, EmbedDistVar a) =>
    SourceFile fmt -> Source (GList a)
  -- | A source file that represents a list-shaped data frame with 1 column
  SourceReadFileField ::
    (FromDataSource fmt rowC fieldC, fieldC a, EmbedDistVar a) =>
    SourceFile fmt -> Source (GList a)
  SourceBind :: (DistVar a -> Source b) -> Source a -> Source b

-- | Type class to turn something into a 'Source', using the identity function
-- if the object is already a 'Source', and using 'SourceData' otherwise
class Sourceable a b where
  toSource :: a -> Source b

type family IsSource a where
  IsSource (Source _a) = 'True
  IsSource _a = 'False

instance Sourceable (Source a) a where
  toSource s = s

instance Sourceable (DistVar a) a where
  toSource VParam = SourceParam
  toSource (VData x) = SourceData x
  toSource (VADT adt) = SourceCtor $ mapADT toSource adt

instance (IsSource a ~ 'False, EmbedDistVar a) => Sourceable a a where
  toSource a = toSource $ embedDistVar a

dvToSource :: DistVar a -> Source a
dvToSource dv = case dv of
  VParam -> SourceParam
  (VData x) -> SourceData x
  (VADT adt) -> SourceCtor $ mapADT dvToSource adt

-- | Map an operation over a 'DistVar' 'GList'
mapSource :: (DistVar a -> Source b) -> DistVar (GList a) -> Source (GList b)
mapSource _ VParam = SourceParam
mapSource _ (VADT Nil) = SourceCtor Nil
mapSource f (VADT (Cons x xs)) =
  SourceCtor (Cons (f x) (mapSource f xs))

--
-- * Reading Data Sources Source DSL Expressions
--

-- | Read a 'SourceFile' as a sequence of bytes
getRaw :: SourceFile f -> IO BS.ByteString
getRaw SourceFile { sourceFile = f } = BS.readFile f

-- | Type class for file formats. The @fmt@ type is a dummy type indicating the
-- format. The @rowC@ and @fieldC@ arguments are class constraints on types that
-- can be read from the format represented by @fmt@: @rowC@ applies to types
-- that can be read as rows, while @fieldC@ applies to types that can be read
-- from a "single-column" data source.
class FromDataSource fmt (rowC :: * -> Constraint)
                         (fieldC :: * -> Constraint)
                         | fmt -> rowC fieldC where
  fetchSource :: (rowC row, EmbedDistVar row) => SourceFile fmt ->
                 IO (DistVar (GList row))
  -- We might need to use a slightly different decoding function if we're trying
  -- to use a data source of something other than tuples, because we need
  -- to account for the 'Only' type as used by SQLite or Cassava or what-have-you
  fetchSourceField :: (fieldC fld, EmbedDistVar fld) =>
                      SourceFile fmt -> IO (DistVar (GList fld))

-- | Convert a 'V.Vector' to a Grappa variable of list type
vecToListVar :: EmbedDistVar a => V.Vector a -> DistVar (GList a)
vecToListVar = F.foldr cons (VADT Nil)
  where cons x xs = VADT (Cons (embedDistVar x) xs)

-- | Interpret a Source DSL Expression as an 'IO' computation
interpSource :: Source a -> IO (DistVar a)
interpSource (SourceData d) = return $ embedDistVar d
interpSource SourceParam = return VParam
interpSource (SourceCtor adt) = VADT <$> traverseADT interpSource adt
interpSource (SourceReadFileRow file) = fetchSource file
interpSource (SourceReadFileField file) = fetchSourceField file
interpSource (SourceBind f x) = do
  x' <- interpSource x
  interpSource (f x')

-- Unfortunately, because we don't have full typing information for
-- the whole program, sometimes we have gprior statements that don't
-- have a concrete type for a source. In this case, we fill in that
-- type as Unused and use the following typeclass to convert the
-- value, often filling in parameters in order to make the types line
-- up. We only ever produced an Unused field when the field is ignored
-- entirely, so this shouldn't change the semantics: if it does, then
-- that's a compiler bug!

data Unused = Unused deriving (Eq, Show, Read)

instance Num Unused where
  Unused + Unused = Unused
  Unused * Unused = Unused
  abs Unused = Unused
  negate Unused = Unused
  signum Unused = Unused
  fromInteger _ = Unused

class AllowUnused a b where
  allowUnused :: Source a -> Source b

type family IsUnused t where
  IsUnused Unused = 'True
  IsUnused _      = 'False

instance {-# INCOHERENT #-} AllowUnused x x where
  allowUnused x = x

instance {-# INCOHERENT #-}  AllowUnused a Unused where
  allowUnused _ = SourceParam

instance AllowUnused t b => AllowUnused (GList t) (GList b) where
  allowUnused SourceParam = SourceParam
  allowUnused (SourceCtor Nil) = SourceCtor Nil
  allowUnused (SourceCtor (Cons x xs)) =
    undefined

instance AllowUnused (GTuple '[]) (GTuple '[]) where
  allowUnused SourceParam = SourceParam
  allowUnused (SourceCtor Tuple0) = SourceCtor Tuple0

instance AllowUnused x y => AllowUnused (GTuple '[x]) (GTuple '[y]) where
  allowUnused SourceParam = SourceParam
  allowUnused (SourceCtor (Tuple1 x)) = SourceCtor (Tuple1 (allowUnused x))

instance (AllowUnused x1 y1, AllowUnused x2 y2) =>
         AllowUnused (GTuple '[x1,x2]) (GTuple '[y1,y2]) where
  allowUnused SourceParam = SourceParam
  allowUnused (SourceCtor (Tuple2 x y)) = SourceCtor (Tuple2 (allowUnused x) (allowUnused y))

instance (AllowUnused x1 y1, AllowUnused x2 y2, AllowUnused x3 y3) =>
         AllowUnused (GTuple '[x1,x2,x3]) (GTuple '[y1,y2,y3]) where
  allowUnused SourceParam = SourceParam
  allowUnused (SourceCtor (Tuple3 a b c)) =
    SourceCtor (Tuple3 (allowUnused a) (allowUnused b) (allowUnused c))

instance (AllowUnused x1 y1, AllowUnused x2 y2, AllowUnused x3 y3, AllowUnused x4 y4) =>
         AllowUnused (GTuple '[x1,x2,x3,x4]) (GTuple '[y1,y2,y3,y4]) where
  allowUnused SourceParam = SourceParam
  allowUnused (SourceCtor (Tuple4 a b c d)) =
    SourceCtor (Tuple4 (allowUnused a) (allowUnused b) (allowUnused c) (allowUnused d))

--
-- * CSV Format
--

-- Cassava CSV parsing for Grappa pairs
instance (Csv.FromField a, Csv.FromField b) =>
         Csv.FromRecord (GTuple '[a, b]) where
  parseRecord = fmap (\(a,b) -> ADT (Tuple2 (Id a) (Id b))) . Csv.parseRecord

-- Cassava CSV parsing for Grappa triples
instance (Csv.FromField a, Csv.FromField b, Csv.FromField c) =>
         Csv.FromRecord (GTuple '[a, b, c]) where
  parseRecord = fmap (\(a,b,c) ->
                       ADT (Tuple3 (Id a) (Id b) (Id c))) . Csv.parseRecord

instance Csv.FromField a => Csv.FromField (Id a) where
  parseField = fmap Id . Csv.parseField

instance (Csv.FromField a, Num a) => Csv.FromField (AD.Forward a) where
  parseField = fmap AD.auto . Csv.parseField

instance Csv.FromField Unused where
  parseField _ = return Unused

-- FIXME HERE: add more instances for tuples
instance (Csv.FromField a, EmbedDistVar a) => Csv.FromField (DistVar a) where
  parseField f
    | f == BS8.pack "" = return VParam
    | otherwise = fmap embedDistVar (Csv.parseField f)

data CSV = CSV deriving (Eq, Show, Read)

instance FromDataSource CSV Csv.FromRecord Csv.FromField where
  fetchSource src = do
    raw <- getRaw src
    case Csv.decode Csv.NoHeader raw of
      Left err -> error err
      Right vs -> return (vecToListVar vs)

  fetchSourceField src = do
    raw <- getRaw src
    case Csv.decode Csv.NoHeader raw of
      Left err -> error err
      Right vs -> return (vecToListVar (fmap Csv.fromOnly vs))

--
-- * JSON Format
--

-- FIXME HERE: this should not be the default way to parse DistVars, because we
-- want missing data to become VParam
instance (Aeson.FromJSON a, EmbedDistVar a) => Aeson.FromJSON (DistVar a) where
  parseJSON = fmap embedDistVar . Aeson.parseJSON

-- JSON parsing for Grappa pairs
instance (Aeson.FromJSON a, Aeson.FromJSON b) =>
         Aeson.FromJSON (GTuple '[a, b]) where
  parseJSON = fmap (\(a,b) -> ADT (Tuple2 (Id a) (Id b))) . Aeson.parseJSON

-- JSON parsing for Grappa triples
instance (Aeson.FromJSON a, Aeson.FromJSON b, Aeson.FromJSON c) =>
         Aeson.FromJSON (GTuple '[a, b, c]) where
  parseJSON = fmap (\(a,b,c) ->
                     ADT (Tuple3 (Id a) (Id b) (Id c))) . Aeson.parseJSON

-- JSON parsing for Grappa lists
instance Aeson.FromJSON a => Aeson.FromJSON (GList a) where
  parseJSON = fmap fromHaskellList . Aeson.parseJSON

instance Aeson.FromJSON Unused where
  parseJSON _ = return Unused

-- FIXME HERE: add more instances for tuples



data JSON = JSON deriving (Eq, Show, Read)

instance FromDataSource JSON Aeson.FromJSON Aeson.FromJSON where
  fetchSourceField = fetchSource
  fetchSource src = do
    raw <- getRaw src
    case Aeson.eitherDecode raw of
      Left err -> error err
      Right vs -> return (vecToListVar vs)
