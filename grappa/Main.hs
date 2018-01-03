{-# LANGUAGE TemplateHaskell #-}

module Main where

import qualified System.Directory as Sys
import qualified System.Environment as Sys
import qualified System.FilePath as Sys
import           System.FilePath ((</>))
import qualified System.Process as Proc

header :: String
header = unlines
  [ "{-# LANGUAGE TemplateHaskell #-}"
  , "{-# LANGUAGE QuasiQuotes #-}"
  , "{-# LANGUAGE ViewPatterns #-}"
  , "{-# LANGUAGE DataKinds #-}"
  , "{-# LANGUAGE ScopedTypeVariables #-}"
  , "{-# LANGUAGE FlexibleContexts #-}"
  , "{-# LANGUAGE ConstraintKinds #-}"
  , "{-# LANGUAGE TypeFamilies #-}"
  , "{-# LANGUAGE TypeFamilies #-}"
  , "{-# OPTIONS_GHC -Wno-all #-}"
  , "module Main where"
  , "import Language.Grappa.Frontend.Compile(grappa)"
  , "import Language.Grappa.Interp"
  , "import Language.Grappa.GrappaInternals"
  , "[grappa|"
  ]

footer :: String
footer = "\n|]\n"

projectPath :: String -> String
projectPath name = basePath </> "." ++ fileName ++ "-project"
  where basePath = Sys.takeDirectory name
        fileName = Sys.takeFileName name

cabalFile :: String -> String
cabalFile name = projectPath name </> "grappa-main.cabal"

sourceFile :: String -> String
sourceFile name = projectPath name </> "Main.hs"

stackFile :: String -> String
stackFile name = projectPath name </> "stack.yaml"

cabalFileText :: String
cabalFileText = unlines
  [ "name: grappa-main"
  , "version: 0.0.1"
  , "build-type: Simple"
  , "cabal-version: >=1.10"
  , ""
  , "executable grappa-main"
  , "  default-language: Haskell2010"
  , "  hs-source-dirs: ."
  , "  main-is: Main.hs"
  , "  ghc-options: -ddump-splices"
  , "  build-depends: base"
  , "               , grappa"
  ]

stackFileText :: FilePath -> String
stackFileText cwd = unlines
  [ "packages:"
  , "- '.'"
  , "- location: " ++ cwd ++ "/"
  , "  extra-dep: true"
  , "resolver: lts-8.8"
  , "extra-deps:"
  , "- alex-tools-0.1.1.0"
  , "- pcg-random-0.1.3.4"
  , "- microtimer-0.0.1.2"
  , "- layout-rules-0.1.0.1"
  ]

main :: IO ()
main = do
  (file:_) <- Sys.getArgs
  Sys.createDirectoryIfMissing False (projectPath file)
  source <- readFile file
  cwd <- Sys.getCurrentDirectory
  writeFile (sourceFile file) (header ++ source ++ footer)
  writeFile (cabalFile file) cabalFileText
  writeFile (stackFile file) (stackFileText cwd)

  let p = (Proc.proc "stack" ["build"]) { Proc.cwd = Just (projectPath file) }
  _ <- Proc.readCreateProcess p ""

  output <- Proc.readCreateProcess ((Proc.proc "stack" ["exec", "grappa-main"]) { Proc.cwd = Just (projectPath file) }) ""
  putStrLn output
  return ()
