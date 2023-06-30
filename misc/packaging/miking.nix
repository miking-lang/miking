{ lib, stdenv, fetchGit,
  binutils-unwrapped,
  coreutils,
  gcc,
  ocaml-ng
}:

let ocamlPackages = ocaml-ng.ocamlPackages_5_0; in

stdenv.mkDerivation rec {
  pname = "miking";
  version = "0.0.0+git";

  # Unlike Guix, Nix does not seem to expose the filter used by the git fetcher.
  # Changing this file will result in another derivation.
  src = fetchGit ../..;

  propagatedBuildInputs = with ocamlPackages;
    [ ocaml
      findlib
      dune_3
      linenoise
      binutils-unwrapped
      gcc.cc

      coreutils  # For sys.mc (mkdir, echo, rm, ...)
      lwt        # For async-ext.mc
      owl        # For dist-ext.mc
      toml       # For toml-ext.mc
    ];

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
    '';
  };
}
