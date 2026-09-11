# MCore interpreter micro-benchmarks

Small, self-contained MCore programs for comparing three evaluators:

| Evaluator | Command | Implementation |
| --- | --- | --- |
| boot | `mi-boot eval prog.mc` | the OCaml interpreter in `src/boot` |
| `mi eval` | `mi eval prog.mc` | `src/stdlib/mexpr/eval.mc`, the self-hosted interpreter |
| fast-eval | `mi eval --fast-eval prog.mc` | `src/stdlib/mexpr/eval-fast.mc`, the experimental evaluator that pre-compiles the AST into nested closures |

## Running

```sh
./run.sh                        # every benchmark, default scales
./run.sh fib loop-sum           # only these
./run.sh -s 20 fib              # override the SCALE parameter
./run.sh -r 5 fib               # best of 5 runs (default 3)
./run.sh -e fast,eval           # skip an evaluator (fast | eval | boot)
./run.sh -t 60                  # per-run timeout in seconds
MI=../build/mi-cheat ./run.sh   # pick a different `mi`
```

The runner reports the best wall-clock time of `-r` runs, and uses the process
exit code as a checksum: if the evaluators disagree the row is flagged
`MISMATCH`.

**Do not wrap the timed command in `timeout`.** The `timeout` on this system
(uutils coreutils 0.8.0, not GNU) rounds the child's elapsed time up to the
next 100ms -- `timeout 60 /bin/true` reports 107ms for a 4ms command -- which
is larger than most of what this suite measures, and it silently turns every
result into a staircase. The runner enforces its `-t` limit with a background
watchdog beside the child instead, which keeps millisecond resolution.

`noop.mc` measures startup, parsing, symbolization and type checking with an
empty program -- about 70ms for `mi`, 5ms for a compiled evaluator from
`../fast-eval-variants`. Subtract it from every other row to get the time
actually spent evaluating.

`--fast-eval` is new, so a stale `build/mi` will reject it with
`ERROR: Unknown option --fast-eval.`; rebuild with `make` (or `make cheat`)
first.

## How the programs are written

Every program ends in `exit (modi <result> 251)`, because the fast evaluator
has no printing primitives. The exit code doubles as a cheap correctness check
across evaluators. Intermediate values are kept small with `modi ... 1000003`
so that 63-bit overflow cannot make the backends disagree.

Each scalable program has exactly one tunable parameter on a line of the form

```
let scale = 27 in -- SCALE
```

which `run.sh -s` rewrites. The header comment of each file says what the
program exercises and how it scales.

## What the fast evaluator supports

`eval-fast.mc` covers a deliberately small subset of MExpr, and the benchmarks
stay inside it so that all three evaluators can run the same source:

* terms: variables, application, lambda, `let`, `recursive let`, `type`,
  `con`, constants, `match`, records, record update, sequences, `never`
* patterns: variable, wildcard, boolean, integer, character, record (so tuples
  too), and both sequence forms -- `PatSeqTot` and `PatSeqEdge`
* constants: `Int` and `Float` arithmetic, shifts, comparisons and conversions;
  `Bool`; `Char` with `eqc`, `int2char` and `char2int`; every sequence constant
  from `get` and `cons` through `foldl`, `foldr` and `create`; `unsafeCoerce`;
  `exit`

Notably absent, and therefore absent from the benchmarks: constructor patterns,
`print` and the rest of I/O, references, tensors, maps, and externals. That also
means nothing from the standard library can be `include`d, since much of it
bottoms out in unsupported primitives. Recursive data still has to be
Church-encoded (see `church-list.mc`), because constructor patterns are not
supported -- which is why that benchmark stays in the suite beside the sequence
ones.

## The benchmarks

| Program | What it exercises | Scaling |
| --- | --- | --- |
| `noop` | startup, parsing, type checking | — |
| `fib` | non-tail recursion, call overhead, wide shallow call tree | exponential |
| `loop-sum` | tail calls in the tightest possible loop | linear |
| `nested-loops` | nested loops, three-argument currying, a closure called from another function | quadratic |
| `deep-rec` | recursion *depth*: `scale` live frames at once | linear |
| `ackermann` | deep recursion plus nested calls in argument position | exponential |
| `tak` | three-argument currying, recursive calls in every argument | steep |
| `mutual-rec` | three-way mutual recursion inside one `recursive` group | linear |
| `mutual-rec-outer` | the same, but reading a variable bound outside the group | linear |
| `closures` | closure allocation and higher-order application chains | quadratic |
| `church-list` | recursive data built from closures, folded three times | linear |
| `records` | record construction, multi-field `{s with ...}`, record patterns | linear |
| `tuples` | tuple construction and patterns, no record update | linear |
| `primes` | trial division: `muli`/`modi` in two nested tail loops | ~scale^1.5 |
| `collatz` | `divi`/`modi` with unpredictable branching | ~linear |
| `bitcount` | the shift constants `slli`/`srli` | linear |
| `env-lookup-shallow` | reading a variable 4 bindings away | linear |
| `env-lookup-deep` | reading a variable 64 bindings away | linear |
| `seq-fold` | `create`, `foldl` and `foldr`: a callback per element | linear |
| `seq-map` | `map` and `mapi`: a fresh sequence per pass | linear |
| `seq-index` | `get` and `length` with no allocation in the loop | linear |
| `seq-build` | `cons`, `snoc`, `concat`, `subsequence`: rope growth | linear |
| `seq-pattern` | `PatSeqEdge`, both `[x] ++ rest` and `[x] ++ mid ++ [y]` | linear |
| `seq-set` | `set`, the only three-argument sequence constant | linear |
| `seq-sort` | merge sort: `splitAt`, patterns, non-tail recursion | n log n |
| `strings` | `int2char`, `char2int`, `eqc` over a character sequence | linear |
| `float-loop` | `addf`/`subf`/`mulf`/`divf` in the tightest loop | linear |
| `float-mandel` | float branching, five-argument currying, nested loops | quadratic |
| `float-points` | floats inside a record, updated field by field | linear |

Three of the benchmarks come in pairs, so that the difference between the two
rows isolates one thing:

* `records` vs `tuples` -- `{s with ...}` against building the record from
  scratch. Note what this does and does not measure: both rewrite *all five*
  fields, so it is the worst case for `TmRecordUpdate` (five nested nodes, five
  `mapInsert`s, five intermediate records) against the best case for
  construction (one `mapMap`, one record). It says nothing about updating one
  field of a wide record, which is the case where update should win outright.
* `env-lookup-shallow` vs `env-lookup-deep` -- the cost of variable lookup
  against scope size, which matters because `eval-fast.mc` represents the
  environment as an association list searched linearly.
* `mutual-rec` vs `mutual-rec-outer` -- the cost of reading a variable from
  outside a multi-binding `recursive` group.
* `records` vs `float-points` -- the same five-field state loop with integers
  and with floats, so the difference is the cost of float values alone.
* `seq-map` vs `seq-build` -- allocation with a callback per element against
  allocation without one.

Apart from `mutual-rec` and `mutual-rec-outer`, every benchmark uses separate
single-binding `recursive` groups even where a single multi-binding group would
read more naturally, so that the pair above is the only place multi-binding
groups are measured.

## A bug this suite surfaced (fixed)

`mutual-rec-outer` used to cost `--fast-eval` about two orders of magnitude more
per iteration than `mutual-rec`, and was quadratic in `scale` — the one row
where `--fast-eval` was an order of magnitude *slower* than `mi eval`. In
`RecLetsEval` in `src/stdlib/mexpr/eval-fast.mc` the `env` inside the fold was
the *accumulator*, which shadowed the environment `reclet` was called with.
Binding *k* of a group therefore tied its knot with `reclet` applied to an
environment that already contained bindings *1..k-1*, so every call to a binding
other than the first prepended another copy of the group to the environment. The
environment grew without bound while the program ran, and anything looked up
below it got further away on every iteration.

```diff
   recursive let reclet = lam env.
     foldl
-      (lam env. lam t.
+      (lam acc. lam t.
         match t with (s, cls) in
-        Cons ((s, VCls (lam val. cls (reclet env) val)), env))
+        Cons ((s, VCls (lam val. cls (reclet env) val)), acc))
       env ts
   in reclet
```

Groups with a single binding were unaffected, since there the accumulator *is*
the incoming environment — which is why the rest of the suite never saw it, and
why the two `mutual-rec` benchmarks are kept at the same scale as a regression
check on it.

## Related

`../fast-eval-variants` holds standalone copies of `eval-fast.mc` that each
change one design decision — environment representation, key type, value type,
staging — and reuses these benchmarks to measure it.
