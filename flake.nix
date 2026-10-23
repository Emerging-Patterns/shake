{
  description = "shake: CLI argument parser for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37)
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # Interim: ez (and bolt, which ez builds) stays on the bend its own flake.lock
  # records, 2.0.36, until ez releases on 2.0.38; ez does not check on 2.0.38
  # yet. A later tooling pass puts `inputs.bend.follows = "bend"` and
  # `ez.mkProofs` back.
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.url = "github:bendlang/bend/eebc18cd04daeade06c3f68c3c96c1faefd3462f";
    inputs.bend.inputs.nixpkgs.follows = "nixpkgs";
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
      # `proofs` does what `ez prove` does, on this flake's bend (2.0.38):
      # every PROOF.bend, its first line `ALL PROOFS CHECK` (interim, until
      # ez runs on 2.0.38 and `ez.mkProofs` comes back). `lint` is bolt at
      # the lock's `[tools.bolt]` pin, on ez's bend, graded by ./bolt.bend.
      checks.${system} = {
        inherit demo;
        proofs = pkgs.runCommand "shake-proofs" {
          nativeBuildInputs = [ bend ];
          BEND_LIB = ez.bendLib ./ez.lock.toml;
        } ''
          export HOME=$TMPDIR
          cp -r ${self} src && chmod -R u+w src && cd src
          for p in $(find . -name PROOF.bend -not -path './.ez/*' | sort); do
            first=$(cd "$(dirname "$p")" && bend "$(basename "$p")" | head -n 1)
            echo "$p: $first"
            [ "$first" = "ALL PROOFS CHECK" ] || exit 1
          done
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
