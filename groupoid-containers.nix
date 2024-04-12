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
      rev = "d182af36a763d0a354f83650a44e5ac8d5c9726f";
      sha256 = "sha256-O/ZMBgkg7d89JqlsT+MZoYtR1E1mGEgNxsNVLXi4F6E=";
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
