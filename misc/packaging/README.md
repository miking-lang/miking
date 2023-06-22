# Packaging utilities

This folder contains package definitions and utilities for distributing Miking.

## Nix package definition

`miking.nix` (and `default.nix`) contain a package definition of Miking for the [Nix](https://nixos.org) package manager.

For users of Nix, a shell containing all development inputs for Miking can be produced by running the following command from this directory.

    $ nix-shell -A miking

To produce a shell with Miking itself, use the following command.

    $ nix-shell -A miking-shell

## Guix package definition

`miking.scm` contains a package definition of Miking for the [Guix](https://guix.gnu.org) package manager.

For users of Guix, a shell containing all development inputs for Miking can be produced by running the following command from this directory.

    $ guix shell -L . -D miking

To produce a shell with Miking itself, use the following command.

    $ guix shell -L . miking

## Self-contained tarball script

`miking-pack` is a shell script which uses the Nix package definition to produce a completely self-contained tarball with Miking and its dependencies for binary distribution.
The current version of the script works only for x86-64 Linux and WSL, but in the future it will also support macOS and ARM.
The script requires Nix to be installed on the build system, and can be run as follows.

    $ /path/to/miking-pack

This produces a tarball `miking-pack.tar.gz` in the current working directory with structure

    miking-pack/
      bin/
        ...
      lib/
        mcore/stdlib/
        ...
      mi
      mi-setup
      ...

The directories `bin/` and `lib/`, et.c., contain the necessary dependencies for the Miking compiler.
`mi-setup` is a shell script which must be run after extracting the tarball to set the dynamic linker path inside the bundled executables, and `mi` runs the Miking compiler itself.
To use this bundle on a system, simply run

    tar xzf miking-pack.tar.gz
    miking-pack/mi-setup

You should then be able to compile Miking programs using, e.g.,

    miking-pack/mi compile my_file.mc

Note that the `mi-setup` command only needs to be run once as an installation procedure.
The `miking-pack` folder can be renamed and moved around freely as long as its internal structure is preserved, but then `mi-setup` must be run again afterwards (and any binaries compiled with the bundled mi will cease to work unless their dynamic linker path is updated as well).

`mi-setup` is a POSIX shell script which depends on the commands `realpath`, `dirname` and `find` usually available on any Unix system (included in coreutils and findutils respectively).

### Implementation

The `miking-pack` script works by the following steps:

1. Invoke `nix-store -qR` to get all the runtime dependencies of Miking and copy them to a temporary directory.

2. Patch the binary-specific shared library paths (using the `patchelf` tool) to point to the bundle's `lib` directory (relative to the file itself using the `$ORIGIN` feature for `rpath`s), and remove a few occurrences of absolute paths inside the dependencies.

3. Create an `mi-setup` script which invokes a statically linked `patchelf` included in the bundle to update the dynamic linker path in all executables to point to the bundled dynamic linker (the path is absolute, so this must be done on the user system).

4. Create a wrapper script `mi` which sets `OCAMLPATH`, `OCAMLLIB`, `PATH`, `LIBRARY_PATH` and `MCORE_LIBS` to point to the right directories within the bundle before invoking the real `mi` executable.  It also sets `OCAMLPARAM` to make the compiled binary get the appropriate dynamic linker and `rpath` paths, and unsets `LD_LIBRARY_PATH` and `OPAM_SWITCH_PREFIX` to ensure they don't interfere with the bundle.

5. Create a tarball containing the above.
