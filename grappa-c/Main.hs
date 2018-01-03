{-# LANGUAGE TemplateHaskell #-}

module Main where

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

sourceFile :: GrappaConfig -> String
sourceFile config = projectPath config </> "Main.hs"

stackFile :: GrappaConfig -> String
stackFile config = projectPath config </> "stack.yaml"

outputPath :: GrappaConfig -> FilePath
outputPath config = takeDirectory (outputFile config)


--
-- * Creating Haskell Source Files
--

hsHeader :: String
hsHeader = unlines
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

hsFooter :: String
hsFooter = "\n|]\n"

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
   [ "resolver: lts-8.8"
   , "extra-deps:"
   , "- alex-tools-0.1.1.0"
   , "- pcg-random-0.1.3.4"
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
defaultConfig name =
  do grappaLib <- lookupEnv "GRAPPA_LIB"
     outputFile <- makeAbsolute (defaultOutputBinary name)
     return $
       GrappaConfig { inputFile = name,
                      projectPath = defaultProjectPath name,
                      outputFile = outputFile,
                      grappaLibPath = grappaLib }

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
  hsSource <- readFile (inputFile config)
  writeFile (sourceFile config) (hsHeader ++ hsSource ++ hsFooter)
  writeFile (cabalFile config) (cabalFileText config)
  writeFile (stackFile config) (stackFileText config)

  let p =
        (proc "stack" ["install", "--local-bin-path", outputPath config])
        { cwd = Just (projectPath config) }
  _ <- readCreateProcess p ""

  return ()
