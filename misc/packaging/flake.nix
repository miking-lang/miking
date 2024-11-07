{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux.pkgs;
      miking = pkgs.callPackage ./miking.nix {};
      shell = pkgs.mkShell {
        name = "Miking dev shell";
        inputsFrom = [ miking ];
        buildInputs = [
          pkgs.tup
          pkgs.ocamlformat
        ];
      };
    in {
      packages.x86_64-linux.default = miking;
      devShells.x86_64-linux.default = shell;
    };
}
