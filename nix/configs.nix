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
        grappa = github "grappa" // { local = /home/kquick/work/grappa; };
        alex-tools = hackageVersion "0.3.1";
        # hmatrix-gsl = githubsrc "haskell-numerics" "hmatrix" // {
        #   # local = /home/kquick/work/AFRL-ADIDRUS-COSMAN/hmatrix;
        #   subpath = "packages/gsl";
        # };
      };
    };

  jobsets = null;  # TBD; relies Briareus to generate jobsets

  lbfgspp = pkgs.callPackage ./lbfgspp.nix {};

  packageset = mkRelease
    { inherit pkgs hydraRun;
      srcs = inputSrcs;
      overrides = {
        global = params: {
          # lapack = pkgs.lapack.override { shared = true; };
        };
        haskell-packages = params: self: super:
          let whichGHC = params.ghcver or default_ghc;
          in
            (with pkgs.haskell.lib; {

              Diff = dontCheck super.Diff; # tests need QuickCheck 2.12 updates
              
              # hmatrix-gsl = appendConfigureFlag super.hmatrix-gsl "-fdisable-default-paths";
              # hmatrix-gsl = addExtraLibrary super.hmatrix-gsl pkgs.openblas;

              hmatrix-gsl =
              let hmatrix-gsl-base = super.callPackage
                    ({ mkDerivation, array, base, gsl, hmatrix, process, random, vector, openblas
                     }:
                       mkDerivation {
                         pname = "hmatrix-gsl";
                         version = "0.19.0.1";
                         sha256 = "0v6dla426x4ywaq59jm89ql1i42n39iw6z0j378xwb676v9kfxhm";
                         libraryHaskellDepends = [
                           array base hmatrix process random vector
                         ];
                         libraryPkgconfigDepends = [ gsl openblas ];
                         description = "Numerical computation";
                         license = pkgs.stdenv.lib.licenses.gpl3;
                       }) {inherit (pkgs) gsl openblas;};
                in let x = addExtraLibraries hmatrix-gsl-base [ pkgs.openblas pkgs.gsl ];
                              in addBuildDepends x  [ pkgs.openblas pkgs.gsl ];

              ad = addExtraLibrary (super.ad) [ pkgs.gmp ];

              layout-rules = markUnbroken super.layout-rules;

              grappa =
                let withDeps =
                      with pkgs; addExtraLibraries
                        (dontHaddock                # Grappa haddocks are currently broken
                          super.grappa
                        )
                        [
                          pkgs.openblas
                          pkgs.eigen
                          pkgs.gsl
                          (pkgs.liblapack.override { shared = true; })
                          lbfgspp
                          pkgs.stack
                          pkgs.pkgconfig
                          pkgs.gmp
                        ];
                in withDeps.overrideAttrs (oldAttrs:
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
                  });
            });
      };
      addSrcs = master-srcs;
      parameters = { inherit ghcver system variant; };
    };

in if hydra-jobsets then jobsets else packageset