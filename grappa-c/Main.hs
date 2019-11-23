{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad (void)
import System.Directory
import System.Environment
import System.FilePath
import System.FilePath ((</>))
import System.Process
import System.Console.GetOpt

--
-- * Configurations
--

-- | Grappa configuration, describing the compilation target, etc.
data GrappaConfig =
  GrappaConfig
  { inputFile :: FilePath,
    -- ^ The Grappa source file we are compiling
    projectPath :: FilePath,
    -- ^ Path where we are going to create our stack project
    outputFile :: FilePath,
    -- ^ The path to the binary that we will create
    grappaLibPath :: Maybe FilePath
    -- ^ The path where the Grappa library is installed locally, if at all
  }

cabalFile :: GrappaConfig -> String
cabalFile config = projectPath config </> "grappa-main.cabal"

mainFile :: GrappaConfig -> String
mainFile config = projectPath config </> "Main.hs"

stackFile :: GrappaConfig -> String
stackFile config = projectPath config </> "stack.yaml"

outputPath :: GrappaConfig -> FilePath
outputPath config = takeDirectory (outputFile config)


--
-- * Creating Haskell Source Files
--

-- | Escape the 'inputFile' of a 'GrappaConfig'
escapeInputFile :: GrappaConfig -> String
escapeInputFile config =
  concatMap (\c -> if c == '"' then ['\\', '"'] else [c]) $
  inputFile config

hsHeader :: GrappaConfig -> String
hsHeader config = unlines
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
  , "import Language.Grappa.Frontend.Compile(compileGrappa,gtext)"
  , "import Language.Grappa.Interp"
  , "import Language.Grappa.GrappaInternals"
  , "$(compileGrappa \"" ++ escapeInputFile config ++ "\" [gtext|"
  ]

hsFooter :: String
hsFooter = "\n|])\n"

cabalFileText :: GrappaConfig -> String
cabalFileText config = unlines
  [ "name: grappa-main"
  , "version: 0.0.1"
  , "build-type: Simple"
  , "cabal-version: >=1.10"
  , ""
  , "executable " ++ takeFileName (outputFile config)
  , "  default-language: Haskell2010"
  , "  hs-source-dirs: ."
  , "  main-is: Main.hs"
  , "  ghc-options: -ddump-splices"
  , "  build-depends: base"
  , "               , grappa"
  ]

stackFileText :: GrappaConfig -> String
stackFileText config =
  let (local_pkgs, extra_deps) =
        case grappaLibPath config of
          Just libPath ->
            ([ "- location: " ++ libPath ++ "/"
             , "  extra-dep: true" ], [])
          Nothing ->
            ([], ["- grappa-1.0"]) in
  unlines
  ([ "packages:"
   , "- '.'" ] ++
   local_pkgs ++
   [ "resolver: lts-12.26"
   , "extra-deps:"
   , "- alex-tools-0.3"
   , "- microtimer-0.0.1.2"
   , "- layout-rules-0.1.0.1"
   ]
   ++ extra_deps)


--
-- * Command-Line Argument Processing
--

-- | Grappa command-line options
data GrappaOption
  = GrappaOutName String

grappaOptions :: [OptDescr GrappaOption]
grappaOptions =
  [ Option "o" [] (ReqArg GrappaOutName "FILE") "output FILE" ]

defaultOutputBinary :: String -> String
defaultOutputBinary name = dropExtension name

defaultProjectPath :: String -> String
defaultProjectPath name = basePath </> "." ++ fileName ++ "-project"
  where basePath = takeDirectory name
        fileName = takeBaseName name

-- | Build a default configuration from an input Grappa filename
defaultConfig :: String -> IO GrappaConfig
defaultConfig inputFile =
  do grappaLibPath <- lookupEnv "GRAPPA_LIB"
     outputFile <- makeAbsolute (defaultOutputBinary inputFile)
     projectPath <- makeAbsolute (defaultProjectPath inputFile)
     return $ GrappaConfig { .. }

-- | Process a command-line option as a modification of a configuration
processOption :: GrappaConfig -> GrappaOption -> GrappaConfig
processOption config (GrappaOutName outName) =
  config { outputFile = outName }

-- | Process the command line into a 'GrappaConfig'
processSysArgs :: IO GrappaConfig
processSysArgs =
  do args <- getArgs
     case getOpt RequireOrder grappaOptions args of
       (opts, [name], []) ->
         do config <- defaultConfig name
            return $ foldl processOption config opts
       (_, _, errs) ->
         ioError (userError (concat errs ++ usageInfo header grappaOptions))
         where header = "Usage: grappa-c [OPTION...] FILE"


--
-- * Top-level Main Function
--

main :: IO ()
main = do
  config <- processSysArgs
  createDirectoryIfMissing False (projectPath config)
  grappaSource <- readFile (inputFile config)
  let mainContents = hsHeader config ++ grappaSource ++ hsFooter
  case grappaLibPath config of
    Just glibPath ->
      do let altMainFile = glibPath </> "grappa-build" </> "Main.hs"
         writeFile altMainFile mainContents
         let p =
               (proc "stack" ["install", "grappa:grappa-build",
                              "--local-bin-path", projectPath config])
               { cwd = Just glibPath }
         void $ readCreateProcess p ""
         copyFile (projectPath config </> "grappa-build") (outputFile config)

    Nothing ->
      do writeFile (mainFile config) mainContents
         writeFile (cabalFile config) (cabalFileText config)
         writeFile (stackFile config) (stackFileText config)
         let p =
               (proc "stack" ["install", "--local-bin-path", outputPath config])
               { cwd = Just (projectPath config) }
         void $ readCreateProcess p ""
