
module Language.Grappa.Interp.CExpr where

-- | The types of C expressions that we are targeting with our compiler
data CType
  = DoubleType
    -- ^ The C type @double@
  | IntType
    -- ^ The C type @int@
  | TupleType [CType]
    -- ^ An array of C values stored consecutively in memory, represented in C
    -- as the type @union value *@
  | FixedListType Int CType
    -- ^ A fixed-length list, represented the same way as a tuple of one type
    -- repeated a fixed number of times
  | VarListType CType
    -- ^ The C type @struct var_length_array*@
  deriving Show

-- | C expressions with a fixed, static value
data Literal
  = DoubleLit Double
  | IntLit Int
  deriving Show

newtype VarName = VarName Int deriving Show

type FunName = String

data UnaryOp = NegateOp | NotOp
             deriving Show

data BinaryOp
  = PlusOp | TimesOp | MinusOp | DivOp | ExpOp
  | LtOp | LteOp | GtOp | GteOp | EqOp | NeOp
  | AndOp | OrOp
  deriving Show

data CExpr
  = LitExpr Literal
  | VarExpr VarName
  | UnaryExpr UnaryOp CExpr
  | BinaryExpr BinaryOp CExpr CExpr
  | FunCallExpr FunName [CExpr]
  | NamedVarExpr String
  | CondExpr CExpr CExpr CExpr
  | TupleProjExpr [CType] CExpr Int
  | FixedListProjExpr CType CExpr CExpr
  | VarListProjExpr CType CExpr CExpr
  deriving Show

instance Num CExpr where
  e1 + e2 = BinaryExpr PlusOp e1 e2
  e1 - e2 = BinaryExpr MinusOp e1 e2
  e1 * e2 = BinaryExpr TimesOp e1 e2
  abs = error "Unimplemented CExpr op!"
  signum = error "Unimplemented CExpr op!"
  negate e = UnaryExpr NegateOp e
  fromInteger i = LitExpr (IntLit (fromInteger i))

instance Fractional CExpr where
  e1 / e2 = BinaryExpr DivOp e1 e2
  fromRational r = LitExpr (DoubleLit (fromRational r))

instance Floating CExpr where
  pi = NamedVarExpr "pi"
  exp e = FunCallExpr "exp" [e]
  log e = FunCallExpr "log" [e]
  sqrt e = FunCallExpr "sqrt" [e]
  e1 ** e2 = BinaryExpr ExpOp e1 e2
  sin e = FunCallExpr "sin" [e]
  cos e = FunCallExpr "cos" [e]
  asin e = FunCallExpr "asin" [e]
  acos e = FunCallExpr "acos" [e]
  atan e = FunCallExpr "atan" [e]
  sinh e = FunCallExpr "sinh" [e]
  cosh e = FunCallExpr "cosh" [e]
  asinh e = FunCallExpr "asinh" [e]
  acosh e = FunCallExpr "acosh" [e]
  atanh e = FunCallExpr "atanh" [e]

data CFunDef = CFunDef FunName [CType] CExpr
             deriving Show

data Dist
  = DoubleDist CExpr [(VarName, CExpr)]
    -- ^ Distribution for a double value with a given PDF and its gradient
  | IntDist CExpr [(VarName, CExpr)]
    -- ^ Distribution for an int value with a given PMF
  | TupleDist [Dist]
    -- ^ Distribution for a fixed sequence of values, each of which is
    -- distributed according to a separate sub-distribution
  | FixedListDist Int Dist
    -- ^ Distribution for a fixed-length list of values, each of which is drawn
    -- IID from the same sub-distribution
  | VarListDist Dist
    -- ^ Distribution for a variable-length list of values, each of which is
    -- drawn IID from the same sub-distribution
  deriving Show

data DPMix =
  DPMix
  { clusterDist :: Dist
  , valuesDist :: Dist
  -- ???
  -- , funDefs :: [CFunDef]
  }
  deriving Show
