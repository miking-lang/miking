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
- `stdlib/uct-implementations.imc`, op-impls connecting the two files above, plus "default" implementations
- `paper-example.mc`, code using the UCT interface

## Debugging and other info

Right now the compiler will print two kinds of debug output:
- Json values representing the complete reptypes problem. These are
  what I feed into some analysis to generate graphs from. *Most
  likely* you won't find much use for this part of the output, but
  maybe.
- Text like `INFO<info>: updated reptype solution closure, took
  0.0029296875ms`. This points at `letimpl` and shows the time it took
  to process it. "Processing" here means computing all possible
  implementation solutions that involve it.

The compiler will also output two pprinted versions of the program to
`out1.html` and `out2.html` in the current directory. These can be
examined in a web browser, they're interactive and clickable (showing
the type of each hovered expression).
- `out1.html`: After the `reptypes-analysis` phase, i.e., we've
  type-checked and figured out which representations must be the same,
  but not substituted operations for actual, concrete implementations.
- `out2.html`: After substituting operations, i.e., all operations,
  `letop`s, and `letimpl`s are gone. Limitation for now: I don't take
  care to properly substitute `Repr` types, instead I just replace
  them with `Unknown` for now (since that's enough for the OCaml
  backend), so `out2.html` will likely contain a fair bit of
  `Unknown`s.
