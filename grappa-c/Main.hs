{-# LANGUAGE RecordWildCards #-}

module Main where

import           CabalBld
import           Control.Monad ( void, when )
import           Control.Monad.IO.Class ( liftIO )
import           Data.Maybe ( catMaybes )
import           Data.Time.Clock ( getCurrentTime )
import qualified DynFlags
import qualified GHC
import           GHC.Paths ( libdir )
import           StackBld
import           StringBuffer ( stringToStringBuffer )
import           System.Console.GetOpt
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.Process


--
-- * Configurations
--

-- | Grappa configuration, describing the compilation target, etc.
data GrappaConfig =
  GrappaConfig
  { inputFile :: FilePath
    -- ^ The Grappa source file we are compiling
  , projectPath :: FilePath
    -- ^ Path where we are going to create our stack or cabal project
  , outputFile :: FilePath
    -- ^ The path to the binary that we will create
  , grappaLibPath :: Maybe FilePath
    -- ^ The path where the Grappa library is installed locally, if at all
  , compileMethod :: CompileMethod
  }

data CompileMethod = Direct | Cabal | Stack


----------------------------------------------------------------------
--
-- * Creating Haskell Source Files
--

-- | Escape the 'inputFile' of a 'GrappaConfig'
escapeInputFile :: GrappaConfig -> String
escapeInputFile config =
  concatMap (\c -> if c == '"' then ['\\', '"'] else [c]) $
  inputFile config

fileBody :: GrappaConfig -> String -> String
fileBody config body = unlines
  [ "{-# LANGUAGE TemplateHaskell #-}"
  , "{-# LANGUAGE QuasiQuotes #-}"
  , "{-# LANGUAGE ViewPatterns #-}"
  , "{-# LANGUAGE DataKinds #-}"
  , "{-# LANGUAGE ScopedTypeVariables #-}"
  , "{-# LANGUAGE FlexibleContexts #-}"
  , "{-# LANGUAGE ConstraintKinds #-}"
  , "{-# LANGUAGE TypeFamilies #-}"
  , "{-# OPTIONS_GHC -Wno-all #-}"
  , "module Main where"
  , "import Language.Grappa.Frontend.Compile ( compileGrappa, gtext )"
  , "import Language.Grappa.Interp"
  , "import Language.Grappa.GrappaInternals"
  , "$(compileGrappa \"" ++ escapeInputFile config ++ "\" [gtext|"
  , body
  , "|])"
  ]


----------------------------------------------------------------------
--
-- * Direct compilation of Grappa sources
--
-- Alternative builds are provided by the --cabal and --stack
-- command-line flags.

-- This build process uses GHC directly to compile the fileBody
-- defined above, with the grappa code substituted into the
-- TemplateHaskell section and passed to the compileGrappa operation.
--
-- This build process takes an optional filepath to the grappa source
-- distribution (usually supplied via the GRAPPA_LIB environment
-- variable).  When this filepath is specified, the executable
-- utilizes the grappa library built from that location; when no
-- filepath is specified, the grappa library must be registered and
-- available in the local GHC package set.
--
-- For both the local library build or the use of a pre-registered
-- grappa library, the GHC pkg environment must already contain all
-- dependencies for the build.  If building using grappa sources for
-- the grappa library, there are multiple packages that must be
-- present to build that library.  If building using a pre-built and
-- registered grappa library, then only that grappa library is
-- required to be present.  The --cabal or --stack options can be used
-- for alternative build processes that will perform automatic
-- dependency fetching.
modelBuild :: String -> Maybe FilePath -> FilePath -> IO ()
modelBuild body grappaLibPath outFile =
  GHC.defaultErrorHandler DynFlags.defaultFatalMessager DynFlags.defaultFlushOut $
  -- n.b. the following is specific to GHC 8.4.  There are changes in
  -- later GHC versions that may require changes here as well.
  GHC.runGhc (Just libdir) $ do
    dflags <- GHC.getSessionDynFlags
    void $ GHC.setSessionDynFlags $
      dflags { GHC.ghcLink = GHC.LinkBinary
             , GHC.ways = [DynFlags.WayDyn]
             , GHC.buildTag = DynFlags.mkBuildTag [DynFlags.WayDyn]
             , GHC.importPaths = catMaybes [ Just "."
                                           , (\p -> p </> "src") <$> grappaLibPath
                                           ]
             , GHC.verbosity = 1
             }
      `DynFlags.gopt_set` GHC.Opt_BuildDynamicToo
      `DynFlags.gopt_set` GHC.Opt_ExternalInterpreter
      `DynFlags.gopt_set` GHC.Opt_PIC

    case grappaLibPath of
      Nothing -> return ()
      Just gp -> liftIO $ runAlexAndHappy gp

    let inp = stringToStringBuffer body

    now <- liftIO $ getCurrentTime
    let hsFile = outFile <> ".hs" -- This also determines the compilation output file name

    -- n.b. Under GHC 8.8.1, the TargetFile is not required to exist,
    -- but for pre-8.8, the file must exist (even if targetContents
    -- supplies the actual inputs).  This also specifies the output
    -- file name (the extension is removed).
    liftIO $ writeFile hsFile ""  -- Remove this as unnecessary when using GHC 8.8 or later

    let target = GHC.Target
          {
            GHC.targetId = GHC.TargetFile hsFile Nothing
          , GHC.targetAllowObjCode = False
          , GHC.targetContents = Just (inp, now)
          }

    GHC.setTargets [ target ]
    r <- GHC.load GHC.LoadAllTargets  -- does the compilation to generate the executable
    liftIO $ do when (GHC.succeeded r) $ do
                  putStrLn $ "Grappa executable: " <> outFile
                  exitSuccess
                putStrLn "Failure building grappa model executable"
                exitFailure

-- The standard GHC build process does *not* know how to run Alex on
-- .x files or Happy on .y files to generate compilable Haskell files.
-- If building using a grappa source library location, the alex and
-- happy operations must be manually performed to obtain the
-- corresponding .hs file before invoking the GHC compile operation.
runAlexAndHappy :: FilePath -> IO ()
runAlexAndHappy gp = do
  let srcDir = gp </> "src" </> "Language" </> "Grappa" </> "Frontend"
      lexerFile = srcDir </> "Lexer.x"
      lexerHs = srcDir </> "Lexer.hs"
      parserFile = srcDir </> "Parser.y"
      parserHs = srcDir </> "Parser.hs"
  genIfNeeded lexerFile lexerHs "alex"
  genIfNeeded parserFile parserHs "happy"
    where
      genIfNeeded inpF outF cmd = do
        inE <- doesFileExist inpF
        otE <- doesFileExist outF
        when (inE && not otE) $ do
          let p = proc cmd [ "-o", outF, inpF ]
          (r,o,e) <- readCreateProcessWithExitCode p ""
          when (r /= ExitSuccess) $ do putStrLn o
                                       putStrLn $ "ERROR: " <> e
                                       putStrLn $ "Running: " <> show p
                                       exitWith r


----------------------------------------------------------------------
--
-- * Command-Line Argument Processing
--

-- | Grappa command-line options
data GrappaOption
  = GrappaOutName String
  | UseCabal (Maybe FilePath)
  | UseStack (Maybe FilePath)

grappaOptions :: [OptDescr GrappaOption]
grappaOptions =
  [ Option "o" [] (ReqArg GrappaOutName "FILE") "output FILE"
  , Option [] ["cabal"] (OptArg UseCabal "DIR" ) "Use cabal v2 to manage build (in optional project dir)"
  , Option [] ["stack"] (OptArg UseStack "DIR") "Use stack (in optional project dir)"
  ]

-- | Build a default configuration from an input Grappa filename
defaultConfig :: String -> IO GrappaConfig
defaultConfig inputFile =
  do grappaLibPath <- lookupEnv "GRAPPA_LIB"
     outputFile <- makeAbsolute (dropExtension inputFile)
     let basePath = takeDirectory inputFile
         fileName = takeBaseName inputFile
     projectPath <- makeAbsolute (basePath </> "." ++ fileName ++ "-project")
     let compileMethod = Direct
     return $ GrappaConfig { .. }

-- | Process a command-line option as a modification of a configuration
processOption :: GrappaConfig -> GrappaOption -> GrappaConfig
processOption config (GrappaOutName outName) = config { outputFile = outName }
processOption config (UseCabal Nothing)      = config { compileMethod = Cabal }
processOption config (UseCabal (Just path))  = config { compileMethod = Cabal, projectPath = path }
processOption config (UseStack Nothing)      = config { compileMethod = Stack }
processOption config (UseStack (Just path))  = config { compileMethod = Stack, projectPath = path }


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
         where header = "Usage: grappa-c [OPTION...] FILE\n\
                        \ \n\
                        \ Set the GRAPPA_LIB environment variable to the grappa source\n\
                        \ tree location to build from grappa, otherwise specify a project\n\
                        \ directory for cabal or stack builds (not necessary for direct\n\
                        \ non-cabal, non-stack builds)."

----------------------------------------------------------------------
--
-- * Top-level Main Function
--

main :: IO ()
main = do
  config <- processSysArgs
  grappaSource <- readFile (inputFile config)
  let libPath = grappaLibPath config
  let outFName = outputFile config
  let mainContents = fileBody config grappaSource
  let bldFunc = case compileMethod config of
        Direct -> modelBuild
        Cabal  -> cabalBuild (projectPath config)
        Stack  -> stackBuild (projectPath config)
  bldFunc mainContents libPath outFName
