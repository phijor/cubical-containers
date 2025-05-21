{
  description = "An Agda Library set up with Nix Flakes";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    let
      inherit (flake-utils.lib) eachDefaultSystem;
    in
    eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        cubical = pkgs.agdaPackages.cubical;
        cubical-categorical-logic = pkgs.callPackage ./cubical-categorical-logic.nix {
          inherit cubical;
        };
        groupoid-containers = pkgs.callPackage ./groupoid-containers.nix {
          inherit cubical;
          inherit cubical-categorical-logic;
        };
      in
      {
        packages.default = groupoid-containers;
        devShells.default = pkgs.mkShell {
          inputsFrom = [ groupoid-containers ];
        };
      }
    );
}
