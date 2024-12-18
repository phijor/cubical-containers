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
    outputs = [ "out" "html" ];
    postPatch = ''
      patchShebangs ./gen-everything.sh
    '';
    buildPhase = ''
      runHook preInstall

      echo 'Generating list of modules...'
      ./gen-everything.sh

      echo 'Checking `Everything.agda`...'
      agda ./Everything.agda

      echo 'Checking `README.agda`...'
      agda ./README.agda

      echo "Generating HTML docs..."
      agda --html --html-dir=$html --highlight-occurrences ./README.agda

      runHook postInstall
    '';
    buildInputs = [cubical cubical-categorical-logic];
    meta = {
      description = "An Agda playground 🛝";
      longDescription = ''
        A longer description of the package.

        Potentially spanning multiple lines.
      '';
      platforms = lib.platforms.all;
    };
  }
