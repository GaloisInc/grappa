let default_ghc = "ghc844"; in

{ nixpkgs ? <nixpkgs>
# ---- release arguments ----
, ghcver ? default_ghc
, variant ? "master"
# ---- release inputs ----
, grappa-src ? null
# ---- arguments for jobset mode ----
, hydra-jobsets ? false
# ---- standard inputs ----
, system ? null
, pkgOverrides ? null
, freshHaskellHashes ? false
# --- internal inputs ---
, devnix ? builtins.fetchTarball { url = https://api.github.com/repos/kquick/devnix/tarball; }
, pkgs ? import nixpkgs ((import devnix).defaultPkgArgs system pkgOverrides freshHaskellHashes)
, project ? null # unused, but needed to cause a rebuild on hydra if this repo changes.
, hydraRun ? false # if true, ignores githubsrc.local specifications
}:

with (import devnix);

let

  inputSrcs = {
    inherit grappa-src;
  };

  github = githubsrc "GaloisInc";

  master-srcs = params:
    let variant = params.variant or "master";
        variantParts = splitBy "\\|" variant;
        branch = let bvp = assocEqListLookup "branch" variantParts;
                 in if bvp == null
                    then removeSuffix "-latest" variant
                    else bvp;
        isPR = builtins.elem "PR" variantParts;
        whichGHC = params.ghcver or default_ghc;
    in {
      haskell-packages = {
        # Add packages here to override the normal
        # source of those packages (e.g. Hackage) and
        # build them from the locations described.
        grappa = github "grappa";
        alex-tools = hackageVersion "0.3.1";
      };
    };

  jobsets = null;  # TBD; relies Briareus to generate jobsets

  lbfgspp = pkgs.callPackage ./lbfgspp.nix {};

  packageset = mkRelease
    { inherit pkgs hydraRun;
      srcs = inputSrcs;
      overrides = {
        global = params: {
        };
        haskell-packages = params: self: super:
          let whichGHC = params.ghcver or default_ghc;
              withLLVM = params.llvm or false;
          in
            (with pkgs.haskell.lib; {

              Diff = dontCheck super.Diff; # tests need QuickCheck 2.12 updates
              
              ad = addExtraLibrary (super.ad) [ pkgs.gmp ];

              layout-rules = markUnbroken super.layout-rules;

              grappa =
                let withDeps =
                      with pkgs; addExtraLibraries
                        (dontHaddock                # Grappa haddocks are currently broken
                          super.grappa
                        ) (grappaDeps ++
                           [
                             pkgs.makeWrapper
                             (pkgs.haskell.packages.${whichGHC}.ghcWithPackages (hpkgs:
                               grappalibDeps ++ [ hpkgs.alex hpkgs.happy ]))
                           ]);
                    grappalibDeps = builtins.filter (x: x != null) super.grappa.propagatedBuildInputs;
                    grappaDeps =
                        [
                          pkgs.openblas
                          pkgs.eigen
                          pkgs.gsl
                          (pkgs.liblapack.override { shared = true; })
                          lbfgspp
                          pkgs.gmp
                          pkgs.gcc
                        ];
                    enhanced = withDeps.overrideAttrs (oldAttrs:
                      {
                        # The grappa package includes some C++ bits that
                        # it normally gets via a submodules checkout.
                        # These packages are separately installed, so
                        # update the local cabal file to find those
                        # installed locations.
                        preConfigurePhases = let o = oldAttrs.preConfigurePhases;
                                             in o ++ ["patchCabalcbits" "patchDummyBuild"];

                        patchCabalcbits = ''
                          sed -i -e 's=include-dirs: =include-dirs: ${pkgs.eigen}/include/eigen3 ${lbfgspp}/include ${pkgs.gsl}/include =' grappa.cabal
                        '';

                        patchDummyBuild = ''
                          cp grappa-build/{DummyBuild,}Main.hs
                        '';

                        # The grappa-c executable needs to be able to
                        # invoke GHC (and underlying compiler +
                        # binutils), with either the grappa library
                        # package available or the grappa library
                        # dependency packages available.  The
                        # following code is adapted from the
                        # nixpkgs/pkgs/development/haskell-modules/with-packages-wrapper.nix
                        # to create a grappa-c wrapper that sets the
                        # environment to enable the presence of these
                        # dependencies.
                        postInstall =
                          let tgtghc = pkgs.haskell.packages.${whichGHC}.ghcWithPackages (hpkgs:
                                grappaDeps ++ grappalibDeps ++ [ hpkgs.alex hpkgs.happy ]);
                              ghcCommand'   = "ghc";
                              ghcCommand = "${ghcCommand'}";
                              ghcCommandCaps= pkgs.lib.toUpper ghcCommand';
                              libDir        = "${tgtghc}/lib/${ghcCommand}-${tgtghc.version}";
                              docDir        = "${tgtghc}/share/doc/ghc/html";
                              packageCfgDir = "${libDir}/package.conf.d";
                              # CLang is needed on Darwin for -fllvm to work:
                              # https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/codegens.html#llvm-code-generator-fllvm
                              llvm          = pkgs.lib.makeBinPath
                                ([ llvmPackages.llvm ]
                                 ++ pkgs.lib.optional stdenv.targetPlatform.isDarwin llvmPackages.clang);
                          in ''
                              . ${pkgs.makeWrapper}/nix-support/setup-hook

                              wrapProgram $out/bin/grappa-c \
                                --set "NIX_${ghcCommandCaps}"        "$out/bin/${ghcCommand}"     \
                                --set "NIX_${ghcCommandCaps}PKG"     "$out/bin/${ghcCommand}-pkg" \
                                --set "NIX_${ghcCommandCaps}_DOCDIR" "${docDir}"                  \
                                --set "NIX_${ghcCommandCaps}_LIBDIR" "${libDir}"                  \
                                --prefix PATH : ${tgtghc}/bin \
                                --prefix PATH : ${pkgs.gcc}/bin \
                                --prefix PATH : ${pkgs.binutils-unwrapped}/bin \
                                ${pkgs.lib.optionalString withLLVM ''--prefix "PATH" ":" "${llvm}"''}
                        '';
                      });
                in enhanced;
            });
      };
      addSrcs = master-srcs;
      parameters = { inherit ghcver system variant; };
    };

in if hydra-jobsets then jobsets else packageset
