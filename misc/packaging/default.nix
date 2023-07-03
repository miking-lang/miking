with import <nixpkgs> {};
let ocamlBase = ocaml-ng.ocamlPackages_5_0.ocaml; in
rec {
  miking = callPackage (import ./miking.nix) {};
  miking-shell = mkShell {
    buildInputs = [ miking ];
  };
  ocaml-with-cc = ocamlBase.overrideAttrs (finalAttrs: previousAttrs: {
    preConfigure = ''AS="cc -c" ASPP="cc -c"'';
  });
}
