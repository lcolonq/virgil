{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    crane = {
      url = "github:ipetkov/crane";
    };
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs = {
        nixpkgs.follows = "nixpkgs";
      };
    };
    st = {
      url = "github:lcolonq/st";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, ... }@inputs:
    inputs.flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import inputs.rust-overlay) ];
        };
        inherit (pkgs) lib;

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          targets = [ "x86_64-unknown-linux-gnu" ];
        };
        craneLib = (inputs.crane.mkLib pkgs).overrideToolchain rustToolchain;
        src = lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            (lib.hasSuffix "\.html" path) ||
            (lib.hasSuffix "\.js" path) ||
            (lib.hasSuffix "\.css" path) ||
            (lib.hasInfix "/assets/" path) ||
            (craneLib.filterCargoSources path type)
          ;
        };
        nativeBuildInputs = [
          pkgs.pkg-config
        ];
        buildInputs = [
          pkgs.openssl.dev
          pkgs.glfw
          pkgs.xorg.libX11 
          pkgs.xorg.libXcursor 
          pkgs.xorg.libXi 
          pkgs.xorg.libXrandr
          pkgs.xorg.libXinerama
          pkgs.libxkbcommon 
          pkgs.xorg.libxcb  
          pkgs.libglvnd
          pkgs.alsa-lib
        ];
        commonArgs = {
          inherit src nativeBuildInputs buildInputs;
          strictDeps = true;
          CARGO_BUILD_TARGET = "x86_64-unknown-linux-gnu";
          inherit (craneLib.crateNameFromCargoToml { inherit src; }) version;
        };
        cargoArtifacts = craneLib.buildDepsOnly (commonArgs // {
          doCheck = false;
        });
        virgil = craneLib.buildPackage (commonArgs // {
          inherit cargoArtifacts;
        });
      in
        {
          packages = {
            inherit virgil;
          };

          devShells.default = craneLib.devShell {
            packages = nativeBuildInputs ++ buildInputs ++ [
              pkgs.trunk
              pkgs.rust-analyzer
              pkgs.glxinfo
              pkgs.cmake
              pkgs.xxd

              # for doomgeneric testing
              pkgs.clang
              pkgs.SDL2
              pkgs.SDL2_mixer
            ];
            NIX_HARDENING_ENABLE = "";
            LD_LIBRARY_PATH = "$LD_LIBRARY_PATH:${
              pkgs.lib.makeLibraryPath [
                pkgs.xorg.libX11 
                pkgs.xorg.libXcursor 
                pkgs.xorg.libXi 
                pkgs.libxkbcommon 
                pkgs.xorg.libxcb  
                pkgs.libglvnd
              ]
            }";
          };
        });
}
