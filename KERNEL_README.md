
# MCore Jupyter Kernel

In addition to the bootstrap interpreter, this repository also contains a
[Jupyter](https://jupyter.org/) kernel for MCore which is based on the
interpreter. The kernel is written in OCaml and directly interfaces with the
evaluation functions of `boot`. It is focused on enabling a large amount of
interoperability between MCore and Python.

## Getting started

Before using the Jupyter kernel you need to install some dependencies.
The Jupyter kernel requires all the base dependencies of the boot interpreter,
and the `pyml` Python bindings for OCaml. For information on how to install
these, see [README.md](./README.md).

Finally, the OCaml package `jupyter-kernel` is needed. This package needs the
`zeromq` C library, so make sure to install it on your system first. On
Debian-based Linux distributions, this can be done with:

```bash
sudo apt-get install libzmq3-dev
```

On macOS, you can install it using brew:

```bash
brew install zeromq
```

Once this is done, `jupyter-kernel` can be installed through `opam`, using:

```bash
opam install jupyter-kernel
```

To compile the Jupyter kernel, use the make target `kernel`:

```bash
make kernel
```

This will create the binary `build/kernel` in the root directory of the project.
Finally, to register the kernel with Jupyter, run the following command from the
project root.

```bash
jupyter kernelspec install src/boot/kernel --user
```

You are now ready to start using the kernel. For example, to start a new Jupyter
notebook using the MCore kernel, go to the project root, run `jupyter notebook`
and select the `MCore` kernel when creating a new notebook. Note that at the
moment, **you must be in the project root when using the kernel**; this will
change in an upcoming release.

## Plotting graphs

It is possible to plot graphs with MCore using the Python library `matplotlib`.
The Jupyter kernel offers integration with `matplotlib` to display plots inline.
Make sure you have `matplotlib` installed (if not, you can install it using
`pip`). Now, when you use `matplotlib`'s plot functions in a notebook cell, the
plots will be displayed as part of the cell's output. For example, you can try running the following in a cell:

```ocaml
let plt = pyimport "matplotlib.pyplot"
let x = [1,2,4,8]
let _ = pycall plt "plot" (x,)
```
