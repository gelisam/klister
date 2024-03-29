{
  description = "A Klister flake";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs    = nixpkgs.legacyPackages.${system};
        overlay = final: prev: {
          klister = prev.callCabal2nix "klister" ./. { };
        };
        haskellPackages = pkgs.haskellPackages.extend overlay;
      in {
        # nix build
        packages.default = haskellPackages.klister;

        # nix develop
        devShells.default = haskellPackages.shellFor {
          withHoogle = true;
          packages = p: [ p.klister ];
          buildInputs = with haskellPackages; [
            cabal-install
            haskell-language-server
            eventlog2html
          ];
          shellHook = ''
            export KLISTERPATH="$(pwd)"/examples/
          '';
        };
      }
    );
}
