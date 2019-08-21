{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-all #-}

module Language.Grappa.Frontend.DataSource where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as BS
import qualified Data.Csv as Csv
import qualified Data.Foldable as F
import           Data.List (isPrefixOf)
import qualified Data.Vector as V
import           GHC.Exts (Constraint)
import qualified Numeric.AD.Mode as AD
import qualified Numeric.AD.Mode.Forward as AD
import qualified Data.Text as T

import           Language.Grappa.GrappaInternals


--
-- * DSL for Data Sources
--

-- | The type of data read from a data source, which could have missing values
data GrappaData a where
  -- | Data all of which is present
  GData :: a -> GrappaData a
  -- | A piece of data that is missing
  GNoData :: GrappaData a
  -- | ADT data, with a head constructor (in @adt@) and data for the arguments,
  -- where pieces of some of the arguments could be missing
  GADTData :: TraversableADT adt => adt GrappaData (ADT adt) ->
              GrappaData (ADT adt)

-- | Test if a piece of data is missing
isMissingGData :: GrappaData a -> Bool
isMissingGData GNoData = True
isMissingGData _ = False

-- | Match 'ADT'-shaped data
matchADTGData :: TraversableADT adt => GrappaData (ADT adt) ->
                 (adt GrappaData (ADT adt) -> ret) -> ret -> ret
matchADTGData GNoData _ ret = ret
matchADTGData (GData (ADT adt)) k _ = k (mapADT (GData . unId) adt)
matchADTGData (GADTData adt) k _ = k adt

-- | Match 'ADT'-shaped data
matchADTGDataMaybe :: TraversableADT adt => GrappaData (ADT adt) ->
                      Maybe (adt GrappaData (ADT adt))
matchADTGDataMaybe dv = matchADTGData dv Just Nothing

-- | Convert list data to a list of data elements, with a Boolean flag on the
-- end indicating if the tail of the list is all missing
matchADTListData :: GrappaData (GList a) -> ([GrappaData a], Bool)
matchADTListData d_list =
  matchADTGData d_list
  (\adt -> case adt of
      Nil -> ([], False)
      Cons d d_list' ->
        let (ds, flag) = matchADTListData d_list' in
        (d:ds, flag))
  ([], True)

-- | Zip two pieces of list data together
--
-- FIXME: could be more efficient if we added special cases for 'GData'
zipGData :: GrappaData (GList a) -> GrappaData (GList b) ->
            GrappaData (GList (GTuple [a, b]))
zipGData d1 d2 = helper (matchADTListData d1) (matchADTListData d2) where
  helper ([], False) _ = GADTData Nil
  helper _ ([], False) = GADTData Nil
  helper (x:xs,end1) (y:ys,end2) =
    GADTData $ Cons (GADTData $ Tuple2 x y) (helper (xs,end1) (ys,end2))
  helper (x:xs,end1) ([], True) =
    GADTData $ Cons (GADTData $ Tuple2 x GNoData) (helper (xs,end1) ([], True))
  helper ([], True) (y:ys,end2) =
    GADTData $ Cons (GADTData $ Tuple2 GNoData y) (helper ([], True) (ys,end2))
  helper ([], True) ([], True) = GNoData


data SourceFile format = SourceFile
  { sourceFile   :: FilePath
  , sourceFormat :: format
  } deriving (Show)

data Source a where
  -- | A fixed piece of data
  SourceData :: a -> Source a
  -- | A "parameter"
  SourceParam :: Source a
  -- | A constructor expression
  SourceCtor :: TraversableADT adt =>
                adt Source (ADT adt) -> Source (ADT adt)
  -- | A source file that represents a list-shaped data frame with 2 or more
  -- columns
  SourceReadFileRow ::
    (FromDataSource fmt rowC fieldC, rowC (GrappaData a)) =>
    SourceFile fmt -> Source (GList a)
  -- | A source file that represents a list-shaped data frame with 1 column
  SourceReadFileField ::
    (FromDataSource fmt rowC fieldC, fieldC (GrappaData a)) =>
    SourceFile fmt -> Source (GList a)
  SourceBind :: (GrappaData a -> Source b) -> Source a -> Source b


-- | Map a data-to-'Source' operation over a list data
mapSource :: (GrappaData a -> Source b) -> GrappaData (GList a) ->
             Source (GList b)
mapSource _ GNoData = SourceParam
mapSource _ (GData (ADT Nil)) = SourceCtor Nil
mapSource _ (GADTData Nil) = SourceCtor Nil
mapSource f (GData (ADT (Cons (Id x) (Id xs)))) =
  SourceCtor (Cons (f (GData x)) (mapSource f (GData xs)))
mapSource f (GADTData (Cons x xs)) =
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
  fetchSource :: rowC (GrappaData row) => SourceFile fmt ->
                 IO (GrappaData (GList row))
  -- We might need to use a slightly different decoding function if we're trying
  -- to use a data source of something other than tuples, because we need
  -- to account for the 'Only' type as used by SQLite or Cassava or what-have-you
  fetchSourceField :: fieldC (GrappaData fld) => SourceFile fmt ->
                      IO (GrappaData (GList fld))

-- | Convert a 'V.Vector' to Grappa data of list type
--
-- FIXME: would be more efficient if we used 'GData' when possible
vecToGData :: V.Vector (GrappaData a) -> GrappaData (GList a)
vecToGData = F.foldr cons (GADTData Nil)
  where cons x xs = GADTData (Cons x xs)

-- | Interpret a Source DSL Expression as an 'IO' computation
--
-- FIXME: this would be more efficient if we avoided building 'SourceCtor' when
-- the data is all there; could do this with a 2-continuation monad
interpSource :: Source a -> IO (GrappaData a)
interpSource (SourceData d) = return $ GData d
interpSource SourceParam = return GNoData
interpSource (SourceCtor adt) = GADTData <$> traverseADT interpSource adt
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
instance (Csv.FromField (GrappaData a), Csv.FromField (GrappaData b)) =>
         Csv.FromRecord (GrappaData (GTuple '[a, b])) where
  parseRecord = fmap (\(a,b) -> GADTData (Tuple2 a b)) . Csv.parseRecord

-- Cassava CSV parsing for Grappa triples
instance (Csv.FromField (GrappaData a), Csv.FromField (GrappaData b),
          Csv.FromField (GrappaData c)) =>
         Csv.FromRecord (GrappaData (GTuple '[a, b, c])) where
  parseRecord = fmap (\(a,b,c) -> GADTData (Tuple3 a b c)) . Csv.parseRecord

-- FIXME HERE: add more instances for tuples

instance (IsAtomic a ~ 'True, Csv.FromField a) =>
         Csv.FromField (GrappaData a) where
  parseField = fmap GData . Csv.parseField

instance Csv.FromField Unused where
  parseField _ = return Unused

data CSV = CSV deriving (Eq, Show, Read)

instance FromDataSource CSV Csv.FromRecord Csv.FromField where
  fetchSource src = do
    raw <- getRaw src
    case Csv.decode Csv.NoHeader raw of
      Left err -> error err
      Right vs -> return (vecToGData vs)

  fetchSourceField src = do
    raw <- getRaw src
    case Csv.decode Csv.NoHeader raw of
      Left err -> error err
      Right vs -> return (vecToGData (fmap Csv.fromOnly vs))

--
-- * JSON Format
--

-- | Add an empty case to JSON parsing that uses 'VParam' for missing data
addEmptyJSONCase :: (Aeson.Value -> Aeson.Parser (GrappaData a)) ->
                    (Aeson.Value -> Aeson.Parser (GrappaData a))
addEmptyJSONCase _ (Aeson.String str)
  | (T.unpack str == "_" || str == T.empty) = return GNoData
addEmptyJSONCase p x = p x

instance {-# OVERLAPPABLE #-}
  (IsAtomic a ~ 'True, Aeson.FromJSON a) =>
  Aeson.FromJSON (GrappaData a) where
  parseJSON = addEmptyJSONCase (fmap GData . Aeson.parseJSON)

instance (IsTypeList ts, Aeson.FromJSON (TupleF ts GrappaData (GTuple ts))) =>
         Aeson.FromJSON (GrappaData (GTuple ts)) where
  parseJSON = addEmptyJSONCase (fmap GADTData . Aeson.parseJSON)

-- NOTE: we only add the empty parsing case for tuples at the top level

{-
-- JSON parsing for parsing nullary Grappa tuples
instance Aeson.FromJSON (TupleF '[] GrappaData r) where
  parseJSON _ = return Tuple0

-- JSON parsing for parsing unary Grappa tuples
instance Aeson.FromJSON (GrappaData a) =>
         Aeson.FromJSON (TupleF '[a] GrappaData r) where
  parseJSON = fmap (Tuple1) . Aeson.parseJSON

-- JSON parsing for Grappa pairs
instance (Aeson.FromJSON (GrappaData a), Aeson.FromJSON (GrappaData b)) =>
         Aeson.FromJSON (TupleF '[a, b] GrappaData r) where
  parseJSON = fmap (\(a,b) -> Tuple2 a b) . Aeson.parseJSON

-- JSON parsing for Grappa triples
instance (Aeson.FromJSON (GrappaData a), Aeson.FromJSON (GrappaData b),
          Aeson.FromJSON (GrappaData c)) =>
         Aeson.FromJSON (TupleF '[a, b, c] GrappaData r) where
  parseJSON = fmap (\(a,b,c) -> Tuple3 a b c) . Aeson.parseJSON

-- JSON parsing for Grappa quadruples
instance (Aeson.FromJSON (GrappaData a), Aeson.FromJSON (GrappaData b),
          Aeson.FromJSON (GrappaData c), Aeson.FromJSON (GrappaData d)) =>
         Aeson.FromJSON (TupleF '[a, b, c, d] GrappaData r) where
  parseJSON = fmap (\(a,b,c,d) -> Tuple4 a b c d) . Aeson.parseJSON

-- JSON parsing for Grappa quintuples and more
instance (Aeson.FromJSON (GrappaData a), Aeson.FromJSON (GrappaData b),
          Aeson.FromJSON (GrappaData c), Aeson.FromJSON (GrappaData d),
          Aeson.FromJSON (GrappaData e), IsTypeList ts,
          Aeson.FromJSON (TupleF ts GrappaData r)) =>
         Aeson.FromJSON (TupleF (a ': b ': c ': d ': e ': ts) GrappaData r) where
  parseJSON =
    fmap (\(a,b,c,d,e,rest) -> TupleN a b c d e rest) . Aeson.parseJSON

-- JSON parsing for Grappa lists
instance Aeson.FromJSON (GrappaData a) =>
         Aeson.FromJSON (GrappaData (GList a)) where
  parseJSON =
    addEmptyJSONCase (fmap vecToGData . Aeson.parseJSON)
-}

instance Aeson.FromJSON Unused where
  parseJSON _ = return Unused


data JSON = JSON deriving (Eq, Show, Read)

instance FromDataSource JSON Aeson.FromJSON Aeson.FromJSON where
  fetchSourceField = fetchSource
  fetchSource src = do
    raw <- getRaw src
    case Aeson.eitherDecode raw of
      Left err -> error err
      Right vs -> return (vecToGData vs)
