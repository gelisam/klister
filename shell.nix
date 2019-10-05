with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-unstable.tar.gz) { };
let this = haskellPackages.callPackage ./default.nix { };
in mkShell {
  buildInputs =  [
    # You can specify a GHC version like so:
    # haskell.packages.ghc843.ghcWithHoogle
    (haskell.packages.ghc865.ghcWithHoogle (hpkgs: with hpkgs; [
      extra
      lens
      megaparsec
      optparse-applicative
      prettyprinter
    ] ++ this.buildInputs ++ this.propagatedBuildInputs))

    haskellPackages.ghcid
    haskellPackages.cabal-install

    # General development
    emacs
    git
    zsh
  ];
}
