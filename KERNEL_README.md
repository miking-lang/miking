
# MCore Jupyter Kernel

In addition to the bootstrap interpreter, this repository also contains a
[Jupyter](https://jupyter.org/) kernel for MCore which is based on the
interpreter. The kernel is written in OCaml and directly interfaces with the
evaluation functions of `boot`. It is focused on enabling a large amount of
interoperability between MCore and Python.

## Jupyter basics

[Jupyter](https://jupyter.org/) provides an ecosystem for writing, documenting
and visualizing code in an interactive way. The _Jupyter Notebook_ is a
literate programming environment for this purpose. Notebooks can contain text,
executable code, display images and more. Notebooks provide support for many languages
by using language-specific _kernels_, which take care of executing the user's
code and producing output for the notebook to display.

To get a quick introducion on how to use Jupyter Notebooks in general, check out
[this tutorial](https://mybinder.org/v2/gh/ipython/ipython-in-depth/master?filepath=binder/Index.ipynb).
https://jupyter.org/ also provides more helpful links and information.

This README will explain how to get started with Jupyter Notebooks for MCore,
and go through all the functionality of the Jupyter MCore kernel. Once you have
installed the kernel in the next section, there is also an interactive notebook
demonstrating MCore and the kernel's capabilities at `JupyterExample.ipynb`.

## Getting started

Before using the Jupyter kernel you need to install some dependencies.
The Jupyter kernel requires all the base dependencies of the boot interpreter
(`dune`, `batteries`, and `linenoise`),
and the `pyml` Python bindings for OCaml. For information on how to install
these, see [README.md](./README.md).

Next, you will need to have Jupyter itself installed.
To install Jupyter using using `pip`, run the following command:

```bash
pip install jupyter
```

Finally, the OCaml package `jupyter-kernel` is needed. This package depends on
the `zeromq` C library, so make sure to install it on your system first. On
Debian-based Linux distributions, this can be done with:

```bash
sudo apt-get install libzmq3-dev
```

On macOS, it can be installed using brew:

```bash
brew install zeromq
```

Once this is done, `jupyter-kernel` can be installed through `opam`, using:

```bash
opam install jupyter-kernel
```

Finally, to install the Jupyter kernel, use the make target `kernel-install`,
by running the following command:

```bash
make kernel-install
```

You are now ready to start using the kernel. For example, to start a new Jupyter
Notebook using the MCore kernel, run `jupyter notebook`
and select the `MCore` kernel when creating a new notebook.

*Note that `$HOME/.local/bin` must be included in your PATH. This should be
done by default on most Linux distributions.*

## Functionality

This section describes all functionality that is supported by the MCore
Jupyter kernel.

### Basic code cells

The Jupyter kernel allows writing and executing code in an interactive manner.
For example, to print the typical 'Hello world!' message, try inputting the following
into a cell and executing it using `Shift-Enter`.

```ocaml
print "Hello world!"
```

The notebook provides syntax highlighting and autocompletion. To trigger the
autocompletion, press `Tab` after inputting part of a word. The completions
include both builtin functions and user-defined names.

### Now you're playing with Python

The MCore kernel also allows executing Python code and interacting with it from
MCore. Use the special directive `%%python` at the top of a cell to evaluate
Python code.

For example, the following cell defines a Python function `foo` and calls it.

```python
%%python
def foo(x):
  print("foo"+x)

foo("bar")
```

The running the cell will print `foobar`, as one might expect.

You can call the functions you have defined in Python cells in normal MCore
cells by using the Python intrinsics (for more information on these, see
[README.md](./README.md) or the example notebook). A user-defined function can
be called by importing and using the Python module `__main__`. For example,
consider the following cell:

```ocaml
let m = pyimport "__main__" in
let x = "bar" in
pycall m "foo" (x,)
```

This cell will call the Python function `foo` defined above, again printing
`foobar` as expected.

### Plotting graphs

It is possible to plot graphs using the Python library `matplotlib`.
The Jupyter kernel offers integration with `matplotlib` to display plots
directly in a notebook.

To use this functionality, first make sure that `matplotlib` is installed (if
not, you can install it using `pip`). Now, when you use `matplotlib`'s plot
functions in a notebook cell, the plots will be displayed as part of the cell's
output. For example, you can try running the following in a cell:

```ocaml
let plt = pyimport "matplotlib.pyplot"
let x = [1,2,4,8]
let _ = pycall plt "plot" (x,)
```

While this example uses the Python intrinsics, running the plot code directly in
a Python cell would of course also work.

## Interactive notebook

If you followed the installation instructions above, you can try out the
interactive example notebook, by running `jupyter notebook` in the root
directory of the repository and opening the file `JupyterExample.ipynb` from the
Jupyter Notebook interface. The notebook features many examples, including MCore
basics and the Python intrinsics, demonstrating the full capabilities of the
MCore Jupyter kernel.
