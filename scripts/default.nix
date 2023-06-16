with import <nixpkgs> {};
{
  miking = callPackage (import ./miking.nix) {};
}
