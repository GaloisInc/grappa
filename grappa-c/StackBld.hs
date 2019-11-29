module StackBld where

import Control.Monad ( when )
import System.Directory
import System.Exit
import System.FilePath
import System.Process
import CabalBld

stackFile :: FilePath -> String
stackFile projectPath = projectPath </> "stack.yaml"


stackFileText :: Maybe FilePath -> String
stackFileText grappaLibPath =
  let (local_pkgs, extra_deps) =
        case grappaLibPath of
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


stackBuild  :: FilePath -> String -> Maybe FilePath -> FilePath -> IO ()
stackBuild projectPath body grappaLibPath outFile =
  case grappaLibPath of
    Just glibPath ->
      do let altMainFile = glibPath </> "grappa-build" </> "Main.hs"
         writeFile altMainFile body
         let p =
               (proc "stack" ["install", "grappa:grappa-build",
                              "--local-bin-path", projectPath])
               { cwd = Just glibPath }
         (r,o,e) <- readCreateProcessWithExitCode p ""
         putStrLn o
         when (not $ null e) $ do putStrLn $ "ERROR: " <> e
                                  putStrLn $ "Running: " <> show p
         when (r == ExitSuccess) $ copyFile (projectPath </> "grappa-build") outFile
         exitWith r

    Nothing ->
      do createDirectoryIfMissing False projectPath
         writeFile (mainFile projectPath) body
         writeFile (cabalFile projectPath) (cabalFileText outFile)
         writeFile (stackFile projectPath) (stackFileText grappaLibPath)
         let p =
               (proc "stack" ["install", "--local-bin-path", takeDirectory outFile])
               { cwd = Just projectPath }
         (r,o,e) <- readCreateProcessWithExitCode p ""
         putStrLn o
         when (not $ null e) $ do putStrLn $ "ERROR: " <> e
                                  putStrLn $ "Running: " <> show p
         exitWith r
