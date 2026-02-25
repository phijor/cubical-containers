{
  description = "An Agda Library set up with Nix Flakes";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      flake = false;
      url = "github:agda/cubical/172b47ab2ddf4fc972734df749ea5abeb47d1346";
    };
    cubical-categorical-logic = {
      flake = false;
      url = "github:um-catlab/cubical-categorical-logic/fe0326bf333ca322869dbbc852c4b21293132146";
    };
    cornelis = {
      url = "github:agda/cornelis";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs =
    inputs@{
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
        cubical = pkgs.agdaPackages.cubical.overrideAttrs (finalAttrs: {
          src = inputs.cubical;
        });
        cubical-categorical-logic = pkgs.callPackage ./cubical-categorical-logic.nix {
          src = inputs.cubical-categorical-logic;
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
          packages = [ inputs.cornelis.packages.${system}.cornelis ];
        };
      }
    );
}
