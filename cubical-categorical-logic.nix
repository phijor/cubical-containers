{
  lib,
  src,

  agdaPackages,
  cubical,
}:
agdaPackages.mkDerivation {
  pname = "cubical-categorical-logic";
  version = "0-unstable-${src.lastModifiedDate}-${src.shortRev}";

  src = lib.sources.cleanSourceWith {
    inherit src;
    filter = name: type: baseNameOf name != "TestEverything.agda";
  };

  buildInputs = [ cubical ];

  meta = {
    description = "Extensions to the cubical stdlib category theory for categorical logic/type theory";
    platforms = lib.platforms.all;
  };
}
