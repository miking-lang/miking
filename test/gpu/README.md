# GPU examples

This has only been tested on Ubuntu 20.04.

## Installation

The `mi` compiler with GPU support can be installed from the `gpu-example`
branch of `git@github.com:larshum/miking.git`.

In addition to the requirements of `mi` itself, the GPU compilation also
requires installing `make`, CUDA and Futhark:
* CUDA is assumed to be installed in `usr/local/cuda`, which is the default
installation directory. Use the following [installation guide](https://docs.nvidia.com/cuda/cuda-installation-guide-linux/index.html).
* To install Futhark, you may follow [these instructions](https://futhark.readthedocs.io/en/stable/installation.html)

## Running examples

### First example program

The example MExpr program `first.mc` contains a function `addOne` that adds one
to a given floating-point number, and two applications of the function. The
second application of `addOne` is requested to run on the GPU by wrapping it in
the `accelerate` construct.

### Compiling and running

To run the example, it must first be compiled into an executable:
```
mi gpu first.mc
```

This command produces an executable `first`. By running it we find that both
applications produce the expected result `26.`.

The same approach used to compile and run the `first.mc` example can be used 
to run the other files in this directory.
