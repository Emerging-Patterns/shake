{
  description = "shake: CLI argument parser for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.36 (the v2.0.36 tag
  # still packages 2.0.35)
  inputs.bend = {
    url = "github:bendlang/bend/eebc18cd04daeade06c3f68c3c96c1faefd3462f";
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
      pkgs = nixpkgs.legacyPackages.${system};
      ez = inputs.ez.lib.${system};
      ezBin = inputs.ez.packages.${system}.default;
      bend = inputs.bend.packages.${system}.default;
      bend-cc = ez.bend-cc;
      demo = ez.mkPackage {
        inherit bend;
        src = self;
        pname = "demo";
        version = "0.5.0"; # x-release-please-version
        entry = "examples/demo/main.bend";
      };
    in {
      packages.${system} = { inherit bend demo bend-cc; ez = ezBin; default = demo; };
      apps.${system}.default = { type = "app"; program = "${demo}/bin/demo"; };
      # `proofs` is `ez prove`: every PROOF.bend on this flake's bend, its
      # first line `ALL PROOFS CHECK`. `lint` is bolt at the lock's
      # `[tools.bolt]` pin, graded by ./bolt.bend.
      checks.${system} = {
        inherit demo;
        proofs = ez.mkProofs { ez = ezBin; src = self; };
        lint = ez.mkLint { src = self; };
      };
      # bolt, from the lock, is on PATH through `src`
      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [ bend bend-cc ezBin ];
      };
    };
}
