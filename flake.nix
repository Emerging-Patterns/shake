{
  description = "shake: CLI argument parser for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      llvm = pkgs.llvmPackages_19;
      bend = inputs.bend.packages.${system}.default;

      bend-cc = pkgs.writeShellScriptBin "bend-cc" ''
        exec ${llvm.clang-unwrapped}/bin/clang \
          -resource-dir ${llvm.clang}/resource-root \
          --ld-path=/usr/bin/ld \
          -Wl,--dynamic-linker=/lib64/ld-linux-x86-64.so.2 "$@"
      '';

      demo = pkgs.stdenv.mkDerivation {
        pname = "shake-demo";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ bend ];
        buildPhase = ''
          bend examples/demo/main.bend -o demo.bin
        '';
        installPhase = ''
          mkdir -p $out/bin
          cp demo.bin $out/bin/demo
        '';
        meta = {
          description = "Fixture CLI for the shake argument parser";
          license = pkgs.lib.licenses.mit;
          mainProgram = "demo";
        };
      };
    in {
      packages.${system} = { inherit bend demo bend-cc; default = demo; };
      apps.${system}.default = { type = "app"; program = "${demo}/bin/demo"; };
      checks.${system} = { inherit demo; };
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend bend-cc ];
        shellHook = "export CC=bend-cc";
      };
    };
}
