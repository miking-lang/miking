{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      mkPkg = system:
        let pkgs = nixpkgs.legacyPackages.${system}.pkgs; in
        rec {
          packages.miking-lib = pkgs.callPackage ./miking-lib.nix {};
          packages.miking-unwrapped = pkgs.callPackage ./miking-unwrapped.nix {
            inherit (packages) miking-lib;
          };
          packages.miking = pkgs.callPackage ./miking.nix {
            inherit (packages) miking-lib miking-unwrapped;
          };
          packages.default = packages.miking;
          devShells.default = pkgs.mkShell {
            name = "Miking dev shell";
            inputsFrom = [ packages.miking-lib packages.miking-unwrapped ];
            buildInputs = [ pkgs.tup pkgs.ocamlformat_0_24_1 ];
          };
        };
    in
      flake-utils.lib.eachDefaultSystem mkPkg // rec {
        overlays.miking = final: prev: {
          miking = final.callPackage ./miking.nix {};
          miking-lib = final.callPackage ./miking-lib.nix {};
          miking-unwrapped = final.callPackage ./miking-unwrapped.nix {};
        };
        overlays.default = overlays.miking;
      };
}
