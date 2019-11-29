module CabalBld where

import Control.Monad ( when )
import System.Directory
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
cabalBuild projectPath body grappaLibPath outFile =
  case grappaLibPath of
    Just glibPath ->
      do let altMainFile = glibPath </> "grappa-build" </> "Main.hs"
         writeFile altMainFile body
         let p = (proc "cabal" ["v2-install", "grappa:grappa-build"
                               , "--installdir=" <> takeDirectory outFile
                               ])
                 { cwd = Just glibPath }
         (r,o,e) <- readCreateProcessWithExitCode p ""
         putStrLn o
         when (not $ null e) $ do putStrLn $ "ERROR: " <> e
                                  putStrLn $ "Running: " <> show p
         exitWith r
  
    Nothing ->
      do createDirectoryIfMissing False projectPath
         writeFile (mainFile projectPath) body
         writeFile (cabalFile projectPath) (cabalFileText outFile)
         let p = (proc "cabal" ["v2-install", takeFileName outFile
                               , "--installdir=" <> takeDirectory outFile
                               ])
                 { cwd = Just projectPath }
         (r,o,e) <- readCreateProcessWithExitCode p ""
         putStrLn o
         when (not $ null e) $ do putStrLn $ "ERROR: " <> e
                                  putStrLn $ "Running: " <> show p
         exitWith r
