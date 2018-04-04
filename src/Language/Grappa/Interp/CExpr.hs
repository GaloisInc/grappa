
module Language.Grappa.Interp.CExpr where

data AtomicType
  = DoubleType
  | IntType
  deriving Show

data CType
  = TupleType [AtomicType]
  | ListType CType
  deriving Show

data Literal
  = DoubleLit Double
  | IntLit Int
  deriving Show

data VarName
  = ParamVar Int
  | ValueVar Int
  deriving Show

type FunName = String

data UnaryOp = NegateOp | NotOp
             deriving Show

data BinaryOp
  = PlusOp | TimesOp | MinusOp | DivOp | ExpOp
  | LTOp | LTEOp | GTOp | GTEOp | EqOp
  | AndOp | OrOp
  deriving Show

data CExpr
  = LitExpr Literal
  | VarExpr AtomicType VarName
  | UnaryExpr UnaryOp CExpr
  | BinaryExpr BinaryOp CExpr CExpr
  | FunCallExpr FunName [CExpr]
  | NamedVarExpr String
  | CondExpr CExpr CExpr CExpr
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

data AtomicDist
  = DoubleDist CExpr [(VarName, CExpr)]
    -- ^ Distribution for a double value with a given PDF and its gradient
  | IntDist CExpr [(VarName, CExpr)]
    -- ^ Distribution for an int value with a given PMF
  deriving Show

data Dist
  = TupleDist [AtomicDist]
    -- ^ Distribution for a fixed sequence of values, each of which is
    -- distributed according to a separate sub-distribution
    {-
  | ListDist Dist
    -- ^ Distribution for a variable-length list of values, each of which is
    -- drawn IID from the same sub-distribution
    -}
  deriving Show

data DPMix =
  DPMix
  { clusterDist :: Dist
  , valuesDist :: Dist
  -- , funDefs :: [CFunDef]
  }
  deriving Show
