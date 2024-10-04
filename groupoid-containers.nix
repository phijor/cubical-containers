{
  agdaPackages,
  cubical,
  cubical-categorical-logic,
  lib,
  ...
}: let
  name = "groupoid-containers";
in
  agdaPackages.mkDerivation {
    pname = name;
    version = "0.1.0";
    src = builtins.path {
      name = "${name}-source";
      path = lib.sources.cleanSource ./.;
    };
    postPatch = ''
      patchShebangs ./gen-everything.sh
    '';
    preBuild = ''
      ./gen-everything.sh
    '';
    buildInputs = [cubical cubical-categorical-logic];
    everythingFile = "./Everything.agda";
    meta = {
      description = "An Agda playground 🛝";
      longDescription = ''
        A longer description of the package.

        Potentially spanning multiple lines.
      '';
      platforms = lib.platforms.all;
    };
  }
