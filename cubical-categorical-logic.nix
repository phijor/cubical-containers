{
  lib,
  fetchFromGitHub,

  agdaPackages,
  cubical,
}:
let
  rev = "feaab165b818fe900bd32eaa387ab350cf1ec4e5";
  version = "2024-09-20-${builtins.substring 0 7 rev}";
  pname = "cubical-categorical-logic";
in
agdaPackages.mkDerivation {
  inherit pname version;

  src = fetchFromGitHub {
    owner = "maxsnew";
    repo = pname;
    inherit rev;
    hash = "sha256-8rSEJD0yNQviBuYsOd6DVySOAsGneJInuoLzc6vq3ow=";
  };

  buildInputs = [ cubical ];

  preConfigure = ''
    make Everything.agda
  '';

  meta = {
    description = "Extensions to the cubical stdlib category theory for categorical logic/type theory";
    platforms = lib.platforms.all;
  };
}
