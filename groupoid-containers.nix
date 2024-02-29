{
  agdaPackages,
  fetchFromGitHub,
  lib,
  name,
  ...
}: let
  cubical = agdaPackages.cubical.overrideAttrs (old: {
    version = "0.7";
    src = fetchFromGitHub {
      owner = "agda";
      repo = "cubical";
      rev = "v0.7";
      sha256 = "sha256-oLpKRWfQqb6CIscC2XM0ia9HJ8edJFHoPeql3kfvyrA=";
    };
  });
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
    buildInputs = [cubical];
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
