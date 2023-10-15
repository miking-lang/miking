# Miking with reptypes

I'm co-opting the readme for the moment, as a way to document things
on how to use reptypes while they're still in flux.

## Minor differences to the paper
* Op-decls are written as `let op : ty = never`.
* Implementations are written in a separate file (extension `.imc`),
  see `uct-implementations.imc`.
* No syntactic sugar for making collections out of sequences
* If the type of a let (or rec-let) binding includes a `Repr` type we
  change it to an op-decl followed by an op-impl. See it as an
  operation that can have at most one op-impl (though multiple
  solutions, that's the point of making it an op instead of a regular
  binding).

## Major differences/limitations that I intend to fix later on
* All implementations are inserted immediately after their op-decl.
  * This means that definitions used must already be in scope, i.e.,
    whatever functions used in the implementations must come *before*
    their op-decl.
  * It also means that impls can only use operations that are declared
    before themselves, so the order they're declared in matters.
* The solver is called in cases where it really doesn't need to be, so
  solving is quite slow.

## Building the compiler

I *think* a normal `make` should work (and put the compiler at
`build/mi`), but I've been using it via `make build-mi` (which uses a
pre-built compiler at `build/mi` to produce `build/mi-tmp`) for
speedier iteration time.

**Important:** I make minor changes to `boot`, so you may need a `make
boot`. If you get syntax errors on `_` in types, this is the cause.

## Examples and how to use things

Reptypes are only available in compiled mode presently, and you must
list any `.imc` files manually. Additionally, in a program using
reptypes many definitions will appear to be dead code since that
analysis happens before we pick implementations (and the former
happens in `boot`, so it's not easy to reorder). Thus
`--keep-dead-code` is an important flag.

```bash
build/mi compile normal-file.mc implementation-file1.imc implementation-file2.imc --keep-dead-code
```

For the moment the only example is `paper-example.mc`, at the root of
the repository. To test it:

```bash
build/mi compile paper-example.mc std.imc stdlib/uct-implementations.imc --keep-dead-code
```

Relevant files:
- `stdlib/collection-interface.mc`, the UCT interface
- `stdlib/uct-implementations.mc`, normal mcore code implementing some representations
- `stdlib/uct-implementations.mc`, op-impls connecting the two files above, plus "default" implementations
- `paper-example.mc`, code using the UCT interface

## Debugging and other info

Right now the compiler will spew a bunch of things as it's
working. It's not pretty, and it's not the most usable output, but
I'll make it better later on.

The debug output might mention `alt`, that's the internal name for the
body of a `letimpl`.

The compiler will also output a pprinted version of the program after
repr solving to `out2.html` in the current directory. Open it in a
browser, it's interactive and clickable. However, I don't take the
care to attach proper types to everything right now, so many types
will be `Unknown`.
