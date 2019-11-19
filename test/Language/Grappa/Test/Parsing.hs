{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

module Language.Grappa.Test.Parsing where

import Test.Hspec

import AlexTools (startPos)
import Language.Grappa.Frontend.AST
import Language.Grappa.Frontend.Parser

tests :: Spec
tests = describe "parsing" $ do
  mapM_ runCase [ justComments
                , basicFun
                , basicModel
                ]

data ParserCase = ParserCase
  { description :: String
  , input  :: String
  , output :: [Decl Raw]
  }

runCase :: ParserCase -> Spec
runCase c = it (description c) $
  case parseDecls (startPos "Test Input") (input c) of
    Left err -> expectationFailure (show err)
    Right rs -> rs `shouldBe` output c

--

fun n cs = FunDecl n Nothing cs
model n cs = FunDecl n Nothing [FunCase [] (ModelExp cs ())]
modelCase p e = ModelCase p (LiteralExp (IntegerLit 1) ()) e

sample x y r = SampleStmt x y r
ret = ReturnStmt
varV n = VarVExp n True ()
varP n = VarPat n ()
varE n = NameExp (LocalName n) ()
binop l op r = OpExp Enabled (Just l) op r
intlit n = LiteralExp (IntegerLit n) ()

justComments :: ParserCase
justComments = ParserCase
  { description = "should ignore comments"
  , input = " -- ignore me!\nfun id x = x"
  , output = [fun "id" [FunCase [varP "x"] (varE "x")]]
  }

basicFun :: ParserCase
basicFun = ParserCase
  { description = "can parse basic functions"
  , input = "fun incr n = n + 1\n"
  , output = [fun "incr"
              [FunCase [varP "n"]  (binop (varE "n") "+" (intlit 1))]]
  }

basicModel :: ParserCase
basicModel = ParserCase
  { description = "can parse basic models"
  , input = "model mapp { n } = n ~ d\n"
  , output =
      [ model "mapp"
          [ modelCase (varP "n")
            (sample (varV "n") (varE "d") ret) ]]
  }
