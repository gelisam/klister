{ mkDerivation, base, call-stack, containers, deepseq, directory
, extra, filepath, hpack, lens, megaparsec, mtl
, optparse-applicative, prettyprinter, stdenv, tasty, tasty-hunit
, text
}:
mkDerivation {
  pname = "klister";
  version = "0.1";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers directory extra filepath lens megaparsec mtl
    prettyprinter text
  ];
  libraryToolDepends = [ hpack ];
  executableHaskellDepends = [
    base containers directory extra filepath lens megaparsec mtl
    optparse-applicative prettyprinter text
  ];
  testHaskellDepends = [
    base call-stack containers deepseq directory extra filepath lens
    megaparsec mtl prettyprinter tasty tasty-hunit text
  ];
  preConfigure = "hpack";
  homepage = "https://github.com/gelisam/klister#readme";
  license = stdenv.lib.licenses.unfree;
  hydraPlatforms = stdenv.lib.platforms.none;
}
