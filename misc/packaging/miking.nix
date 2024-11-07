{ lib, stdenv,
  coreutils,
  makeWrapper,
  ocamlPackages,
  writeText
}:

with ocamlPackages;

stdenv.mkDerivation (finalAttrs: rec {
  pname = "miking";
  version = "0.0.0+git";

  withLwt = true;   # For async-ext.mc
  withToml = true;  # For dist-ext.mc
  withOwl = true;   # For toml-ext.mc

  src = ../..;

  nativeBuildInputs = [
    makeWrapper
    menhir
    dune_3
    coreutils
    ocaml
    findlib
    linenoise
  ]
    ++ lib.lists.optional finalAttrs.withLwt lwt
    ++ lib.lists.optional finalAttrs.withOwl owl
    ++ lib.lists.optional finalAttrs.withToml toml;

  propagatedBuildInputs = [
    coreutils  # Miking currently requires mkdir to be able to run
    ocaml
    findlib
    linenoise
  ];

  makeFlags = [ "prefix=$(out)" "ocamllibdir=$(out)/lib/ocaml/${ocaml.version}/site-lib" ];

  preConfigure = ''
    for f in $(find misc -type f -a -executable); do patchShebangs --build $f; done
  '';

  postInstall = ''
    wrapProgram $out/bin/mi \
      --suffix PATH : ${coreutils}/bin \
      --prefix PATH : ${ocaml}/bin \
  '';

  # doCheck = true;
  # checkTarget = "test-compile";

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
    description     = "Meta language system for creating embedded DSLs";
    homepage        = "https://miking.org";
    license         = licenses.mit;
    longDescription = ''
      Miking (Meta vIKING) is a meta language system for creating
      embedded domain-specific and general-purpose languages.  The
      system features a polymorphic core calculus and a DSL definition
      language where languages can be extended and composed from
      smaller fragments.

      Note: Depending on the target runtime, miking requires the presence of
      additional packages within an environment, such as dune, ocaml, findlib
      and a C compiler for native builds, node for javascript, and a suitable JDK
      when targeting the JVM.
    '';
  };
})
