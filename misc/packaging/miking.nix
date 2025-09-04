{ lib, runCommand, stdenv,
  coreutils,
  makeWrapper,
  ocamlPackages,
  writeText,
  miking-lib, miking-unwrapped,
}:

with ocamlPackages;

let
  args = {
    nativeBuildInputs = [ makeWrapper ];

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
  };
in

runCommand "miking" args ''
  mkdir -p $out/bin
  makeWrapper ${miking-unwrapped}/bin/mi $out/bin/mi \
    --prefix-each PATH : "${coreutils}/bin ${ocaml}/bin ${findlib}/bin ${stdenv.cc}/bin" \
    --prefix-each OCAMLPATH : "${miking-lib}/lib/ocaml/${ocaml.version}/site-lib ${linenoise}/lib/ocaml/${ocaml.version}/site-lib" \
    --prefix MCORE_LIBS : stdlib=${miking-lib}/lib/mcore/stdlib \

''
