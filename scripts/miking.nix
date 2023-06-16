{ lib, stdenv, fetchFromGitHub,
  ocaml-ng,
}:

let ocamlPackages = ocaml-ng.ocamlPackages_5_0; in

stdenv.mkDerivation rec {
  pname = "miking";
  version = "0.0.1";

  src = fetchFromGitHub {
    owner = "miking-lang";
    repo = "miking";
    rev = "fb0e67d781cb24b8c2d25693286054a845d64112";
    sha256 = "16ixfrrn9ns3ypr7c4krpham1lx32i801d12yv0f4y3fl8fn5vv2";
  };

  nativeBuildInputs = with ocamlPackages;
    [ ocaml
      findlib
      dune_2
      linenoise
    ];

  propagatedBuildInputs = with ocamlPackages;
    [ ocaml
      findlib
      dune_2
      linenoise
    ];

  # preBuild = ''
  #   substituteInPlace make.sh --replace 'OCAMLPATH=' 'OCAMLPATH=$OCAMLPATH:'
  #   substituteInPlace Makefile \
  #     --replace 'MCORE_LIBS=' 'OCAMLPATH=\${OCAMLPATH}:`pwd`/build/lib MCORE_LIBS='
  # '';

  installPhase = ''
    dune install --prefix $out # --libdir $out/lib/ocaml/site-lib
    cp build/mi $out/bin
    mkdir -p $out/lib/mcore
    cp -r stdlib $out/lib/mcore
  '';

  dontTest = true;

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
