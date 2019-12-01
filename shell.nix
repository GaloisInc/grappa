let pkgs = import <nixpkgs> {};
    grappa-c = (pkgs.callPackage ./nix/configs.nix {}).grappa;
    lcl_grappa-c = grappa-c.overrideAttrs (oldAttrs: { src = ./.; });
    lcldev_grappa-c = lcl_grappa-c.env.overrideAttrs (oldAttrs: {
      shellHook = ''
        # Set this to build the local diretory grappa library instead of using the installed version.
        export GRAPPA_LIB=$(pwd)

        # When grappa-c is run with --cabal or --stack, it will use
        # GRAPPA_INCDIRS to find any additional includes needed to
        # build the grappa library (e.g. eigen, which also has an additional
        # subdirectory specification).
        export GRAPPA_INCDIRS=$(for I in $(echo $NIX_CFLAGS_COMPILE | tr ' ' '\n' | ag eigen | sort -u); do
                                  if [ -d $I/eigen3 ] ; then echo $I/eigen3 ; else echo $I; fi;
                                done)

        # Ensure any NIX-provided libraries are available at link time.
        export LD_LIBRARY_PATH=$(echo $(echo $NIX_LDFLAGS | tr ' ' '\n' | sed -n -e '/-L/s,^-L,,p') | tr ' ' :):$LD_LIBRARY_PATH;
        grappa-c () {
          cabal run grappa-c \
              $(for I in $(echo $NIX_CFLAGS_COMPILE | tr ' ' '\n' | ag eigen | sort -u); do
                  if [ -d $I/eigen3 ] ; then echo --extra-include-dirs=$I/eigen3 ;
                  else echo --extra-include-dirs=$I ; fi
                done;) \
              -- "$@"
        }
        echo Use the command grappa-c to \(build and\) run the grappa-c compiler with
        echo appropriate local environment settings.  You may want to unset GRAPPA_LIB
        echo to build against a pre-registered grappa haskell library.
      '';
    });
in lcldev_grappa-c
