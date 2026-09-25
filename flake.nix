{
  description = "shake: CLI argument parser for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      ez = inputs.ez.lib.${system};
      ezBin = inputs.ez.packages.${system}.default;
      bend = inputs.bend.packages.${system}.default;
      bend-cc = ez.bend-cc;
      demo = ez.mkPackage {
        inherit bend;
        src = self;
        pname = "demo";
        version = "0.2.0"; # x-release-please-version
        entry = "examples/demo/main.bend";
      };
    in {
      packages.${system} = { inherit bend demo bend-cc; ez = ezBin; default = demo; };
      apps.${system}.default = { type = "app"; program = "${demo}/bin/demo"; };
      # `proofs` is `ez prove`: every PROOF.bend must print exactly
      # `All terms check.` first. `lint` is bolt at the lock's `[tools.bolt]`
      # pin, graded by ./bolt.bend.
      checks.${system} = {
        inherit demo;
        proofs = ez.mkProofs { ez = ezBin; src = self; name = "shake-proofs"; };
        lint = ez.mkLint { src = self; };
      };
      # bolt, from the lock, is on PATH through `src`
      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [ bend bend-cc ezBin ];
      };
    };
}
