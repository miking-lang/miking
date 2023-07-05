with import <nixpkgs> {
  overlays =
    [ (pkgs-self: pkgs-super:
      { ocamlPackages =
          if pkgs-super.stdenv.isDarwin then
            pkgs-super.ocaml-ng.ocamlPackages_5_0.overrideScope' (self: super: {
              ocaml = super.ocaml.overrideAttrs (finalAttrs: previousAttrs: {
                preConfigure = ''AS="cc -c" ASPP="cc -c"'';
              });
              owl-base = super.owl-base.overrideAttrs (finalAttrs: previousAttrs: {
                version = "1.1";
                src = pkgs-super.fetchurl {
                  url = "https://github.com/owlbarn/owl/releases/download/${finalAttrs.version}/owl-${finalAttrs.version}.tbz";
                  hash = "sha256-mDYCZ2z33VTEvc6gV4JTecIXA/vHIWuU37BADGl/yog=";
                };
                meta = {
                  inherit (previousAttrs.meta) description homepage changelog maintainers license;
                };
              });
              owl = super.owl.overrideAttrs (finalAttrs: previousAttrs: {
                inherit (self.owl-base) version src meta;
                preBuild = ''
                  export OWL_CFLAGS="-g -O3 -Ofast -funroll-loops -ffast-math -DSFMT_MEXP=19937 -msse2 -fno-strict-aliasing"
                '';
                hardeningDisable = [ "strictoverflow" ];
              });
            })
          else
            pkgs-super.ocaml-ng.ocamlPackages_5_0;
      })
    ];
};
rec {
  miking = callPackage (import ./miking.nix) {};
  miking-shell = mkShell {
    buildInputs = [ miking ];
  };
}
