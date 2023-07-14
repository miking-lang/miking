{ lib, stdenv,
  coreutils,
  makeWrapper,
  ocamlPackages
}:

with ocamlPackages;

stdenv.mkDerivation rec {
  pname = "miking";
  version = "0.0.0+git";

  # Unlike Guix, Nix does not seem to expose the filter used by the git fetcher.
  # Each new commit will result in a different derivation.
  src = fetchGit {
    url = ../..;
    ref = "HEAD";
  };

  nativeBuildInputs = [
    ocaml
    findlib
    dune_3
    makeWrapper

    lwt        # For async-ext.mc
    owl        # For dist-ext.mc
    toml       # For toml-ext.mc
  ];

  buildInputs = [
    coreutils  # Miking currently requires mkdir to be able to run
    linenoise
  ];

  makeFlags = [ "prefix=$(out)" "ocamllibdir=$(out)/lib/ocaml/${ocaml.version}/site-lib" ];

  postInstall = ''
    wrapProgram $out/bin/mi \
      --suffix PATH : ${coreutils}/bin \
      --suffix OCAMLPATH : ${linenoise}/lib/ocaml/${ocaml.version}/site-lib
  '';

  doCheck = true;
  checkTarget = "test-compile";

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
}
