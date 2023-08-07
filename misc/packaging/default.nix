import <nixpkgs> {
  overlays =
    [ (pkgs-self: pkgs-super:
      { ocamlPackages =
          if pkgs-super.stdenv.isDarwin then
            pkgs-super.ocaml-ng.ocamlPackages_5_0.overrideScope' (ocaml-self: ocaml-super: {
              ocaml = ocaml-super.ocaml.overrideAttrs (finalAttrs: previousAttrs: {
                preConfigure = ''AS="cc -c" ASPP="cc -c"'';
              });
              eigen = ocaml-super.eigen.overrideAttrs (finalAttrs: previousAttrs: {
                meta = {
                  inherit (previousAttrs.meta) homepage description maintainers license;
                };
                preBuild = ''
                  export EIGENCPP_OPTFLAGS="-Ofast -funroll-loops -ffast-math"
                  export EIGEN_FLAGS="-O3 -Ofast -funroll-loops -ffast-math"
                '';
              });
              owl-base = ocaml-super.owl-base.overrideAttrs (finalAttrs: previousAttrs: {
                src = pkgs-super.fetchFromGitHub {
                  owner = "mseri";
                  repo  = "owl";
                  rev   = "9420a4cd04cd7483580264996001ae57a64fad62";
                  hash  = "sha256-f8+YM/N4wjT40ZdoBZNziRNIH13dZ+L+JUEBj/vZa9k=";
                };
                meta = {
                  inherit (previousAttrs.meta) description homepage changelog maintainers license;
                };
              });
              owl = ocaml-super.owl.overrideAttrs (finalAttrs: previousAttrs: {
                propagatedBuildInputs = [ ocaml-self.eigen ] ++ previousAttrs.propagatedBuildInputs;
                preBuild = ''
                  export OWL_CFLAGS="-g -O3 -Ofast -funroll-loops -ffast-math -DSFMT_MEXP=19937 -fno-strict-aliasing"
                  export OWL_AEOS_CFLAGS="-g -O3 -Ofast -funroll-loops -ffast-math -DSFMT_MEXP=19937 -fno-strict-aliasing"
                '';
              });
            })
          else
            pkgs-super.ocaml-ng.ocamlPackages_5_0;
        miking = with pkgs-self; callPackage (import ./miking.nix) {};
        miking-shell = pkgs-super.mkShell {
          buildInputs = [ pkgs-self.miking ];
        };
      })
    ];
}
