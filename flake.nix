{
  description = "An Agda Library set up with Nix Flakes";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:agda/cubical";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
  };
  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      cubical,
      ...
    }:
    let
      inherit (flake-utils.lib) eachDefaultSystem;
    in
    eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ cubical.overlays.default ];
        };
        cubical-categorical-logic = pkgs.callPackage ./cubical-categorical-logic.nix {
          inherit (pkgs) cubical;
        };
        groupoid-containers = pkgs.callPackage ./groupoid-containers.nix {
          inherit (pkgs) cubical;
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
