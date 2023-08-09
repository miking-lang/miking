# Packaging utilities

This folder contains package definitions and utilities for distributing Miking.

## Nix package definition

`miking.nix` (and `default.nix`) contain a package definition of Miking for the [Nix](https://nixos.org) package manager.

For users of Nix, a shell containing all development inputs for Miking can be produced by running the following command from this directory.

    $ nix-shell -A miking

To produce a shell with Miking itself, use the following command.

    $ nix-shell -A miking-shell

To support native compilation, ocaml, findlib, dune and a C compiler must also be added to the environment.

## Guix package definition

`miking.scm` contains a package definition of Miking for the [Guix](https://guix.gnu.org) package manager.

For users of Guix, a shell containing all development inputs for Miking can be produced by running the following command from this directory.

    $ guix shell -L . -D -f miking.scm

To produce a shell with Miking itself, use the following command.

    $ guix shell -L . -f miking.scm

To support native compilation, ocaml, findlib, dune and a C compiler must also be added to the environment.

## Self-contained tarball scripts

The scripts `miking-pack-linux` and `miking-pack-darwin` use the Nix package definition to produce a completely self-contained tarball with Miking and its dependencies for binary distribution.
The former works for x86-64 Linux and WSL, and the latter works for x86-64 and arm64 macOS.
The scripts requires Nix to be installed on the build system, and can be run as follows.

    $ /path/to/miking-pack-linux  # or $ /path/to/miking-pack-darwin

This produces a tarball `miking-pack.tar.gz` in the current working directory with structure

    miking-pack.XXXXXX/  # XXXXXX is a random string generated at build time
      bin/
        ...
      lib/
        mcore/stdlib/
        ...
      mi
      mi-setup  # only on Linux
      ...

The directories `bin/` and `lib/`, et.c., contain the necessary dependencies for the Miking compiler, and `mi` runs the Miking compiler itself.
The Linux version further includes a shell script `mi-setup` which must be run after extracting the tarball to set the dynamic linker path inside the bundled executables.
To use this bundle on a system, simply run

    $ tar xzf miking-pack.tar.gz
    $ miking-pack.XXXXXX/mi-setup  # only on Linux

You should then be able to compile Miking programs using, e.g.,

    $ miking-pack.XXXXXX/mi compile my_file.mc

Note that the `mi-setup` script on Linux only needs to be run once as an installation procedure.
The `miking-pack.XXXXXX` folder can be renamed and moved around freely as long as its internal structure is preserved, but then `mi-setup` must be run again afterwards, and any binaries compiled with the bundled `mi` will cease to work.

`mi-setup` is a POSIX shell script which depends on the commands `realpath`, `dirname` and `find` usually available on any Unix system (included in coreutils and findutils respectively).

The tarball includes everything needed for `test-compile` to pass, including a C compiler, OCaml, `owl` and C library dependencies.

### Implementation

The `miking-pack` script works roughly by the following steps:

1. Invoke `nix-store -qR` to get all the runtime dependencies of Miking and copy them to a temporary directory.

2. Patch the shared library paths of copied binaries (using `patchelf` on Linux or `install_name_tool` on macOS) to point to the bundle's `lib` directory, and remove a few occurrences of absolute paths.

3. On Linux, create an `mi-setup` script which invokes a statically linked `patchelf` included in the bundle to update the dynamic linker path in all executables to point to the bundled dynamic linker (the path is absolute, so this must be done on the user system).
   On macOS, the system's dynamic linker `/usr/lib/dyld` is used instead.

4. Create a wrapper script `mi` which sets `OCAMLPATH`, `OCAMLLIB`, `PATH`, `LIBRARY_PATH` and `MCORE_LIBS` to point to the right directories within the bundle before invoking the real `mi` executable.  It also sets `OCAMLPARAM` to make the binaries compiled by `mi` get the appropriate rpaths, and unsets a few variables to ensure they don't interfere with the bundle.

5. Create a tarball containing the above.
