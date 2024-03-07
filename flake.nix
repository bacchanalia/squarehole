{
  description = ''
    Conrol.Monad.SquareHole
  '';

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat.url = "https://flakehub.com/f/edolstra/flake-compat/1.tar.gz";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachSystem [
      "x86_64-linux"    "aarch64-linux"
      "x86_64-darwin"   "aarch64-dawrin"
      "x86_64-windows"
    ] (system: with nixpkgs.legacyPackages.${system}; let
      pkg = haskell.packages.ghc981.callCabal2nix "squarehole" ./. {};
    in {
      packages = {
        default = pkg;
      };

      devShells.default = self.packages.${system}.default.env;
    });
}
