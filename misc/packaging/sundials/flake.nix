{
  description = "Builds the Miking compiler with Sundials support";

  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs";
    nixpkgs-sundials-5_7_0.url = # SundialsML does not support Sundials after 6.1.1
      "github:nixos/nixpkgs/4953d87fcb07b258561320044f96a25e0754427d";
  };

  outputs = { self, opam-nix, flake-utils, nixpkgs, nixpkgs-sundials-5_7_0 }:
    let sundialsml = "sundialsml";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        pkgs-sundials-5_7_0 = nixpkgs-sundials-5_7_0.legacyPackages.${system};
      in {
        legacyPackages = let
          inherit (opam-nix.lib.${system}) queryToScope;
          inherit pkgs;
          # Build SundialsML from its OPAM package
          scope = queryToScope { } {
            ${sundialsml} = "*";
            # The following line forces opam to choose the compiler from opam
            # instead of the nixpkgs one
            # ocaml-base-compiler = "*";
          };
          buildInputs = with pkgs.ocamlPackages; [
            ocaml
            findlib
            (pkgs-sundials-5_7_0.sundials.override ({ kluSupport = false; }))
          ];
        in scope.overrideScope' (final: prev: {
          ${sundialsml} = prev.${sundialsml}.overrideAttrs (_: {
            buildInputs = buildInputs;
            nativeBuildInputs = buildInputs;
          });
        });

        devShells.default = pkgs.mkShell {
          name = "Miking dev shell";
          buildInputs = with pkgs.ocamlPackages; [
            pkgs.coreutils # Miking currently requires mkdir to be able to run
            ocaml
            linenoise
            pkgs.minizinc
          ];
          nativeBuildInputs = with pkgs.ocamlPackages; [
            ocaml
            findlib
            dune_3
            ocamlformat_0_24_1
            pkgs.gdb

            lwt # For async-ext.mc
            owl # For dist-ext.mc
            toml # For toml-ext.mc
            self.legacyPackages.${system}.${sundialsml} # for sundials-ext.mc
          ];
        };
      });
}
