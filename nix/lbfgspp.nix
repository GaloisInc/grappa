{ stdenv, fetchFromGitHub }:
stdenv.mkDerivation {
  name = "lbfgspp-0.1";

  src = fetchFromGitHub {
    owner  = "yixuan";
    repo = "LBFGSpp";
    rev = "8fb4c24cec812a5358abc379b7dde03afa0db591";
    sha256 = "1xymrl60vsj7ldvx6w32rqhwwd5zg9457aazyc8gy0hfxsdhzlyw";
  };

  installPhase = ''
    mkdir -p $out/include
    cp -r $src/include/* $out/include/
  '';

  meta = {
    description = "A header-only C++ library for L-BFGS algorithm";
    homepage = https://lbfgspp.statr.me;
    license = stdenv.lib.licenses.mit;
    platforms = stdenv.lib.platforms.unix;
  };
}
