{

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Grappa.Frontend.Lexer (
    lexer,
    Token(..),
    Keyword(..),
    Lexeme(..),
    SourcePos(..),
    SourceRange(..)
  ) where


import           AlexTools
import           Data.Char (isAscii)
import qualified Data.Text as T
import qualified Data.Text.Read as T

}

$upper  = [A-Z]
$lower  = [a-z]
$number = [0-9]
$op     = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]

@ident    = $lower [$upper $lower $number _]*
@conident = $upper [$upper $lower $number _]*
@op       = $op [$op]*
@rational = [$number]+ \. [$number]+
@integer  = [$number]+

:-

<0> {

-- skip whitespace
$white+ ;

-- skip comments that begin with "-- "
"--" .* ;

-- skip comments between "{-" and "-}"
"{-" ( ([^\-] | \n)* ("-"[^\}])? )* "-}" ;

"("         { keyword K_lparen    }
")"         { keyword K_rparen    }
"["         { keyword K_lbracket  }
"]"         { keyword K_rbracket  }
"{"         { keyword K_lbrace    }
"}"         { keyword K_rbrace    }
"="         { keyword K_equals    }
"~"         { keyword K_tilde     }
","         { keyword K_comma     }
"_"         { keyword K_under     }
"|"         { keyword K_bar       }
"-"         { keyword K_minus     }
"\"         { keyword K_backslash }
"->"        { keyword K_arrow     }
"<-"        { keyword K_larrow    }
"::"        { keyword K_coloncolon }
".."        { keyword K_dotdot    }
":"         { keyword K_colon     }
"Dist"      { keyword K_Dist      }
"model"     { keyword K_model     }
"fun"       { keyword K_fun       }
"if"        { keyword K_if        }
"then"      { keyword K_then      }
"else"      { keyword K_else      }
"let"       { keyword K_let       }
"in"        { keyword K_in        }
"case"      { keyword K_case      }
"of"        { keyword K_of        }
"source"    { keyword K_source    }
"from"      { keyword K_from      }
"read"      { keyword K_read      }
"as"        { keyword K_as        }
"nothing"   { keyword K_nothing   }
"main"      { keyword K_main      }
"using"     { keyword K_using     }
"param"     { keyword K_param     }

\" [^\"]* \" { mkStrLit }

@ident      { textLexeme TIdent }
@conident   { textLexeme TConIdent }
@op         { textLexeme TOp }
@rational   { readerLexeme T.rational TRat }
@integer    { readerLexeme T.decimal TInt }

.           { lexeme TError }

}


{
-- Lexer -----------------------------------------------------------------------

data Token = TKeyword  !Keyword
           | TIdent    !T.Text
           | TConIdent !T.Text
           | TStrLit   !T.Text
           | TOp !T.Text
           | TInt !Integer
           | TRat !Rational
           | TError
           | TInStart
           | TInEnd
           | TInSep
             deriving (Show)

data Keyword = K_lparen
             | K_rparen
             | K_lbrace
             | K_rbrace
             | K_lbracket
             | K_rbracket
             | K_equals
             | K_under
             | K_bar
             | K_tilde
             | K_comma
             | K_minus
             | K_backslash
             | K_arrow
             | K_larrow
             | K_coloncolon
             | K_dotdot
             | K_colon
             | K_Dist
             | K_model
             | K_fun
             | K_if
             | K_then
             | K_else
             | K_let
             | K_in
             | K_case
             | K_of
             | K_source
             | K_read
             | K_from
             | K_as
             | K_nothing
             | K_main
             | K_using
             | K_param
             | K_ATOMIC
             | K_TUPLE
             | K_CTOR
               deriving (Show, Eq)

keyword :: Keyword -> Action () [Lexeme Token]
keyword kw = lexeme (TKeyword kw)

textLexeme :: (T.Text -> Token) -> Action () [Lexeme Token]
textLexeme f = matchText >>= \t -> lexeme (f t)

-- TODO: actually implement escape chars!
mkStrLit :: Action () [Lexeme Token]
mkStrLit = matchText >>= \t -> lexeme (go t)
  where go = TStrLit . T.tail . T.init

readerLexeme :: T.Reader a -> (a -> Token) -> Action () [Lexeme Token]
readerLexeme reader f =
  textLexeme (\t -> case reader t of
                      Right (res, _) -> f res
                      Left _ -> TError)

data Error = E_lexical !SourcePos
             deriving (Show)

lexer :: SourcePos -> String -> [Lexeme Token]
lexer start str = $makeLexer simpleLexer input
  where
  input = (initialInput (sourceFile start) (T.pack str)) { inputPos = start }

alexGetByte = makeAlexGetByte $ \ c ->
  if isAscii c
     then toEnum (fromEnum c)
     else 0x1
}
