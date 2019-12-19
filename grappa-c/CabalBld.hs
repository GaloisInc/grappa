module CabalBld where

import Control.Monad ( unless, when )
import Data.Maybe ( fromMaybe )
import System.Directory
import System.Environment ( lookupEnv )
import System.Exit
import System.FilePath
import System.Process

mainFile :: FilePath -> String
mainFile projectPath = projectPath </> "Main.hs"

cabalFile :: FilePath -> String
cabalFile projectPath = projectPath </> "grappa-main.cabal"

cabalFileText :: FilePath -> String
cabalFileText outputFile = unlines
  [ "name: grappa-main"
  , "version: 0.0.1"
  , "build-type: Simple"
  , "cabal-version: >=1.10"
  , ""
  , "executable " ++ takeFileName outputFile
  , "  default-language: Haskell2010"
  , "  hs-source-dirs: ."
  , "  main-is: Main.hs"
  , "  ghc-options: -ddump-splices"
  , "  build-depends: base"
  , "               , grappa"
  ]


cabalBuild :: FilePath -> String -> Maybe FilePath -> FilePath -> IO ()
cabalBuild projectPath body grappaLibPath outFile = do
  (bldTarget, inDir) <-
      case grappaLibPath of
        Just glibPath -> do
          -- Use the source grappa.cabal file and generate the main in
          -- the source directory's grappa-build directory
          let altMainFile = glibPath </> "grappa-build" </> "Main.hs"
          writeFile altMainFile body
          return ("grappa:grappa-build", glibPath)
  
        Nothing -> do
          -- Write a .cabal file and a Main.hs to the specified project directory
          createDirectoryIfMissing False projectPath
          writeFile (mainFile projectPath) body
          writeFile (cabalFile projectPath) (cabalFileText outFile)
          return (takeFileName outFile, projectPath)
                   
  let inclArg i = "--extra-include-dirs=" ++ i
  extra_incl <- (map inclArg . words . fromMaybe []) <$> lookupEnv "GRAPPA_INCDIRS"

  -- Ideally this could just be a "cabal v2-install
  -- --extra-include-dirs=... --installdir=..." except that--as of Nov
  -- 2019--the v2-install operation will ignore the
  -- --extra-include-dirs.  The v2-build must be used to observe the
  -- --extra-include-dirs, but then the v2-install will try to rebuild
  -- from an sdist, so manually obtain the output and install it.
                
  let p1 = (proc "cabal" (["v2-build", bldTarget] ++ extra_incl))
           { cwd = Just inDir }
      report t p e = when (not $ null e) $ do putStrLn $ t <> ": " <> e
                                              putStrLn $ "Running: " <> show p
      warn = report "WARNING"
      errs = report "ERROR"
      procRes quiet p r o e = do
        unless quiet $ putStrLn o
        case r of
          ExitSuccess -> warn p e
          _ -> errs p e >> exitWith r
  putStrLn "Compiling grappa code (may take 2-3 minutes)..."
  (r1,o1,e1) <- readCreateProcessWithExitCode p1 ""
  procRes False p1 r1 o1 e1

  -- n.b. do not use cabal v2-install here.  That will generate an
  -- sdist and then perform a build from the sdist [and at the present
  -- time---2019 Nov--it will ignore the --extra-include-dir
  -- specifications, which is probably a bug].

  putStrLn "Built executable, installing..."
  let p2 = (proc "cabal" ["v2-exec"
                         , "bash", "--", "-c", "type -fp grappa-build; echo"])
           { cwd = Just inDir }
  (r2,o2,e2) <- readCreateProcessWithExitCode p2 ""
  procRes True p2 r2 o2 e2

  let p3 = (proc "install" [ head (words o2), outFile ])
           { cwd = Just inDir }
  (r3,o3,e3) <- readCreateProcessWithExitCode p3 ""
  procRes False p3 r3 o3 e3

  putStrLn $ "Compiled grappa to " <> outFile
  exitWith r3
