{
  description = "shell for building virgil";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-unstable;
    naersk.url = "github:nix-community/naersk";
  };

  outputs = { self, nixpkgs, naersk }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      naersk' = pkgs.callPackage naersk {};
      buildInputs = [
        pkgs.pkgconfig
        pkgs.freetype
        pkgs.SDL2
        pkgs.SDL2_image
        pkgs.SDL2_mixer
        pkgs.llvm
        pkgs.clang
        pkgs.llvmPackages.libclang
        pkgs.openssl
      ];
      shell = pkgs.mkShell {
        inherit buildInputs;
        LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
      };
      virgil = naersk'.buildPackage {
        inherit buildInputs;
        src = ./.;
      };
    in {
      defaultPackage.x86_64-linux = virgil;
      devShell.x86_64-linux = shell;
      packages.x86_64-linux = {
        inherit virgil shell;
      };
    };
}
