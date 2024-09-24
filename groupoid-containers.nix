{
  agdaPackages,
  fetchFromGitHub,
  lib,
  name,
  ...
}: let
  cubical = agdaPackages.cubical.overrideAttrs (old: {
    version = "${old.version}-wildcats";
    src = fetchFromGitHub {
      owner = "agda";
      repo = "cubical";
      rev = "502b1bb8a47fb8c07d82e1bc05020d5b4f10cede";
      sha256 = "sha256-UOjI63wVoIIyAfMjAV2aQpU8wOnQiNZokDdxl168n7g=";
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
