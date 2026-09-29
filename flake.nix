{
  description = "shake: CLI argument parser for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend/777ee0b55c485afdd7e68bd917b3d23a88d77371";
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
        version = "0.2.0"; # x-release-please-version
        entry = "examples/demo/main.bend";
      };
    in {
      packages.${system} = { inherit bend demo bend-cc; ez = ezBin; default = demo; };
      apps.${system}.default = { type = "app"; program = "${demo}/bin/demo"; };
      # `proofs` is `bend src/PROOF.bend`: its first line must be
      # `ALL PROOFS CHECK`. `lint` is bolt at the lock's `[tools.bolt]`
      # pin, graded by ./bolt.bend.
      checks.${system} = {
        inherit demo;
        proofs = pkgs.runCommand "shake-proofs" {
          nativeBuildInputs = [ bend ];
          BEND_LIB = ez.bendLib ./ez.lock.toml;
        } ''
          export HOME=$TMPDIR
          cp -r ${self} src && chmod -R u+w src && cd src
          first=$(cd src && bend PROOF.bend | head -n 1)
          echo "src/PROOF.bend: $first"
          [ "$first" = "ALL PROOFS CHECK" ] || exit 1
          touch $out
        '';
        lint = ez.mkLint { src = self; };
      };
      # bolt, from the lock, is on PATH through `src`
      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [ bend bend-cc ezBin ];
      };
    };
}
