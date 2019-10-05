{ pkgs ? import <nixpkgs> { }
}:

with pkgs; mkShell {
  buildInputs = [
    (texlive.combine {
      inherit (texlive)
      # Core
      scheme-basic
      euenc
      latexmk
      # General
      cleveref
      dirtytalk
      # fullpage
      float
      listings
      fancyvrb
      todonotes
      xkeyval
      # Math
      amsmath
      mathtools
      # Graphics
      pgf
      xcolor;
    })
  ];
}
