with import <nixpkgs> {};
rec {
  miking = callPackage (import ./miking.nix) {};
  miking-shell = mkShell {
    buildInputs = [ miking ];
  };
}
