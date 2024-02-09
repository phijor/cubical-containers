{
  description = "An Agda Library set up with Nix Flakes";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = {
    self,
    nixpkgs,
    flake-utils,
    ...
  }: let
    inherit (flake-utils.lib) simpleFlake defaultSystems;
    name = "groupoid-containers";
    overlay = final: prev: {
      ${name} = {
        defaultPackage = final.callPackage ./groupoid-containers.nix {
          inherit name;
        };
      };
    };
  in
    simpleFlake {
      inherit self nixpkgs name overlay;
      systems = defaultSystems;
      shell = {pkgs}:
        pkgs.mkShell {
          inputsFrom = [pkgs.${name}.defaultPackage];
        };
    };
}
