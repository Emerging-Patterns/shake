{
  description = "shake: CLI argument parser for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37)
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forEach = nixpkgs.lib.genAttrs systems;
      outputsFor = system:
        let
          ez = inputs.ez.lib.${system};
          ezBin = inputs.ez.packages.${system}.default;
          bend = inputs.bend.packages.${system}.default;
          bend-cc = ez.bend-cc;
          demo = ez.mkPackage {
            inherit bend;
            src = self;
            pname = "demo";
            version = "0.7.0"; # x-release-please-version
            entry = "examples/demo/main.bend";
          };
        in {
          packages = { inherit bend demo bend-cc; ez = ezBin; default = demo; };
          apps.default = { type = "app"; program = "${demo}/bin/demo"; };
          # `proofs` is `ez prove` on this flake's bend: every PROOF.bend must
          # print `ALL PROOFS CHECK`. `lint` is bolt at the lock's `[tools.bolt]`
          # pin, graded by ./bolt.bend.
          checks = {
            inherit demo;
            proofs = ez.mkProofs { ez = ezBin; src = self; };
            lint = ez.mkLint { src = self; };
          };
          # bolt, from the lock, is on PATH through `src`
          devShells.default = ez.mkShell {
            src = self;
            packages = [ bend bend-cc ezBin ];
          };
        };
      perSystem = forEach outputsFor;
      each = name: forEach (system: perSystem.${system}.${name});
    in {
      packages = each "packages";
      checks = each "checks";
      apps = each "apps";
      devShells = each "devShells";
    };
}
