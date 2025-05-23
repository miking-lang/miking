{ lib, stdenv, nix-gitignore,
  ocamlPackages, miking-lib,
}:

with ocamlPackages;

stdenv.mkDerivation (finalAttrs: {
  pname = "miking";
  version = "0.0.0+git";

  src = nix-gitignore.gitignoreSource "/misc/packaging\n/result\n" ../..;

  nativeBuildInputs = [
    miking-lib
    dune_3
    ocaml
    linenoise
    findlib
    menhir
  ];

  makeFlags = [
    "prefix=$(out)"
    # NOTE(vipa, 2025-06-09): We want to make it possible to supply a
    # different library, thus we stop the Makefile's attempts to use a
    # local stdlib and ocamlpath
    "SET_STDLIB="
    "SET_OCAMLPATH="
  ];

  buildFlags = [ "bootstrap" ];

  installTargets = [ "install-mi" ];

  preConfigure = ''
    for f in $(find misc -type f -a -executable); do patchShebangs --build $f; done
  '';

  meta = with lib; {
    mainProgram     = "mi";
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
