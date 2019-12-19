let pkgs = import <nixpkgs> {};
in (pkgs.callPackage ./nix/configs.nix {}).grappa
