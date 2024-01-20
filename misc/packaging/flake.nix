{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let pkgs = nixpkgs.legacyPackages.x86_64-linux.pkgs;
    in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        name = "Miking dev shell";
        # NOTE(vipa, 2023-09-21): The dependencies below are mirrored
        # from miking.nix. Normally we would like to use miking.nix
        # directly via inputsFrom, but miking.nix is presently not
        # written to work in pure mode so we can't use it here.
        buildInputs = with pkgs.ocaml-ng.ocamlPackages_5_0; [
          pkgs.coreutils  # Miking currently requires mkdir to be able to run
          linenoise
          pkgs.minizinc
        ];
        nativeBuildInputs = with pkgs.ocaml-ng.ocamlPackages_5_0; [
          ocaml
          findlib
          dune_3
          ocamlformat_0_24_1
          pkgs.gdb

          lwt        # For async-ext.mc
          owl        # For dist-ext.mc
          toml       # For toml-ext.mc
        ];
      };
    };
}
