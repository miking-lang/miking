{ lib, stdenv, nix-gitignore, writeText,
  ocamlPackages,
}:

with ocamlPackages;

stdenv.mkDerivation (finalAttrs: {
  pname = "miking-lib";
  version = "0.0.0+git";

  src = nix-gitignore.gitignoreSource [] ../..;

  nativeBuildInputs = [
    dune_3
    ocaml
    linenoise
    findlib
    menhir
  ];

  makeFlags = [ "prefix=$(out)" "ocamllibdir=$(out)/lib/ocaml/${ocaml.version}/site-lib" ];

  buildFlags = [ "boot" ];

  installTargets = "install-boot install-stdlib";

  preConfigure = ''
    for f in $(find misc -type f -a -executable); do patchShebangs --build $f; done
  '';

  setupHook = writeText "setupHook.sh" ''
    addMCorePath() {
      echo test $1
      for dir in "''$1"/lib/mcore/*; do
        export MCORE_LIBS="''${MCORE_LIBS-}''${MCORE_LIBS:+:}''$(basename ''$dir)=''$dir"
      done
    }
    addEnvHooks "$targetOffset" addMCorePath
  '';

  meta = with lib; {
    description     = "Meta language system for creating embedded DSLs, standard library";
    homepage        = "https://miking.org";
    license         = licenses.mit;
    longDescription = ''
      The supporting libraries needed to run the Miking compiler.
    '';
  };
})
