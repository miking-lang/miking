# `eval-fast.mc` design variants

Fourteen standalone copies of `src/stdlib/mexpr/eval-fast.mc`, each changing
**exactly one** design decision and leaving everything else alone, so that the
difference between a variant and the baseline measures that one decision rather
than a combination.

`v10`-`v13` measure something slightly different from `v01`-`v09`: rather than
a decision proposed by this suite, they surface fragments that `eval-fast.mc`
itself already carries -- written as an in-place experiment, then left in the
file but never wired into the real `MExprEvalF` composition. `v00-baseline.mc`
uses only what is actually composed today; each of `v10`-`v13` swaps in one of
those dormant alternatives in its place, so the suite can check whether they
are worth composing without having to trust that call in isolation.

One of them runs the other way. Constant fusion was measured here, found to
pay everywhere, and folded into `eval-fast.mc` itself; `v07-no-fusion` takes it
back out again. A reversion measures the same decision a forward variant does,
and keeping it means the suite goes on checking that the optimisation still
earns its keep as the evaluator grows.

The curried `applyF` went the other way. It was folded in too, then measured at
**1.00x** once a timing bug was fixed -- the tuple allocation is real, but
OCaml's minor heap makes it free at this granularity -- so it was reverted out
of `eval-fast.mc` and `v08-apply-curried` is a forward variant again.

Each file is a complete program: the evaluator, followed by a runner that
parses, symbolizes and type checks the `.mc` file named on the command line the
same way `mi eval` does, then evaluates it. They are not libraries and do not
include one another.

## Building and running

```sh
cd miking
for f in fast-eval-variants/v*.mc; do
  ./build/mi compile "$f" --output "fast-eval-variants/bin/$(basename "$f" .mc)"
done

cd fast-eval-variants
./run-variants.sh                  # every variant over ../experiments
./run-variants.sh -b fib,loop-sum  # only these benchmarks
./run-variants.sh -v v00,v07       # only these variants
./run-variants.sh -r 5             # best of 5 (default 3)
```

`run-variants.sh` uses the exit code of each benchmark as a checksum: every
variant must agree with every other on every benchmark, or the row is flagged
`MISMATCH`.

**Do not wrap the timed command in `timeout`.** The `timeout` here (uutils
coreutils 0.8.0) rounds the child's elapsed time up to the next 100ms, which is
larger than most differences between these variants; it made an earlier round
of measurements a 100ms staircase and several fine-grained conclusions were
wrong as a result. The runner uses a background watchdog for its `-t` limit
instead. The floor is 5ms, so anything doing 150ms of work or more resolves
cleanly. Benchmarks and scales come from `../experiments`, so the two
directories stay in step.

## The variants

| File | Decision it changes | Baseline behaviour |
| --- | --- | --- |
| `v00-baseline.mc` | — | `List (Int, Val)` environment, `Int` keys, `Val` syn, staged |
| `v01-env-seq.mc` | environment is a builtin sequence | a `List` from `list.mc` |
| `v02-env-map.mc` | environment is `Map Int Val` | a linear list |
| `v03-key-symbol.mc` | keys are `Symbol`, compared with `eqsym` | `Int` from `sym2hash` |
| `v04-key-name.mc` | keys are `Name`, compared with `nameEq` | `Int` from `sym2hash` |
| `v05-ret-expr.mc` | values are `Expr` | a dedicated `Val` syn |
| `v06-unstaged.mc` | match the AST on every step | `mkEvalF` builds closures once |
| `v07-no-fusion.mc` | *reverts* fusion: every application goes through `applyF` | saturated constant applications call the delta function directly |
| `v08-apply-curried.mc` | `applyF` takes its argument beside the scrutinee | `applyF` takes a `(Val, Val)` pair |
| `v09-shallow-pats.mc` | lower nested patterns first, then assume shallow ones | `mkTryMatch` recurses into sub-patterns |
| `v10-match-patconmap.mc` | build a constructor -> branches dispatch map for long `PatCon` chains | a linear chain of `eqi` tag comparisons |
| `v11-match-lazy.mc` | build `thn`/`els` lazily, forcing only the branch taken | both branches' closures are built eagerly |
| `v12-reclets-alist.mc` | `recursive let` bindings via `map`/`foldl` over a builtin sequence | `list.mc`'s `List`, via `foldl`/`listReverse`/`listFoldl` |
| `v13-reclets-lazy.mc` | defer building the `recursive let` bindings list with a `Lazy` thunk | built eagerly, every time the group is evaluated |

Three of these change the *shape* of the evaluator rather than a data structure:

* **`v06-unstaged`** is the ordinary alternative to what `eval-fast.mc` does. It
  replaces `mkEvalF : Expr -> EvalFEnv -> Val` with
  `evalF : EvalFEnv -> Expr -> Val`, so matching the AST node, reading
  `nameGetSym`/`sym2hash` out of every variable and binder, and rebuilding the
  delta closure for every constant all move from build time to run time. It
  cannot keep constant fusion -- that happens while compiling, and this
  evaluator never compiles. So `v06` against `v00` prices staging *and* fusion
  together; `v06` against `v07-no-fusion` prices staging alone, which over this
  suite is about 1.9x.
* **`v07-const-fused`** looks at the shape of an application while compiling:
  when a constant is applied to exactly as many arguments as it takes, it pulls
  the function out of `mkDeltaF` once and calls it directly, instead of building
  and immediately destructing a `VConst2`/`VConst1` chain on every evaluation.
  Constants used as values still take the general path.
* **`v09-shallow-pats`** runs `lowerAll` from `mexpr/shallow-patterns.mc`
  between type checking and `mkEvalF`, so every `match` tests one level of one
  constructor with variables or wildcards underneath. `mkTryMatch` then stops
  building a sub-matcher per field or element: it reads the names to bind at
  build time and emits a type test, a length test where there is one, and a
  fixed number of indexed reads. Sequence-edge patterns collapse furthest --
  lowering leaves `minLength` wildcards and nothing else, so what remains at run
  time is a single `geqi`. The lowering is itself an extra pass over the AST and
  makes the AST bigger, which is the other half of what this variant measures.

  `lowerAll` also emits a couple of discarded `let` bindings with no name at
  all, and builds an error message with `print` on the fallthrough of every
  lowered match. Both used to need an accommodation in this variant (a
  `LetEvalF` case that evaluates a nameless binding for effect and binds
  nothing, and its own `IOEvalF` fragment) that the baseline has since grown on
  its own -- `LetEvalF` already falls back to a fresh symbol for an
  unsymbolized binding, and `IOEvalF` is already composed -- so `v09` needs no
  extra fragment of its own any more.

Four more swap in a fragment `eval-fast.mc` already carries but does not
compose:

* **`v10-match-patconmap`** replaces `MatchEvalFEager` with
  `MatchEvalFEager + MatchEvalFEagerPatConMap`. Once a chain of `match x with
  C1 ... else match x with C2 ... else ...` on the same target variable has at
  least `minPatConChain` (5) `PatCon` arms, it builds a `Map Int (List alt)`
  from constructor tag to branch once, while compiling, and does one
  `mapLookup` at run time instead of trying each arm's `eqi` tag comparison in
  order. `../experiments/tree-pattern.mc` (2 constructors) never crosses the
  threshold; `../experiments/variant-pattern.mc` (20 constructors) always
  does. This was tried in place in `eval-fast.mc` and measured no speedup on
  this suite -- keeping it as an isolated variant means that result can be
  re-checked instead of taken on faith.
* **`v11-match-lazy`** replaces `MatchEvalFEager` with `MatchEvalFLazy`, which
  wraps `thn`/`els` in a `lazy.mc` thunk instead of building both up front,
  with a fast path when `els` is `never`.
* **`v12-reclets-alist`** replaces `RecLetsEvalFList` with `RecLetsEvalF`, the
  original alist encoding of a `recursive let` group's bindings (`map` and
  `foldl` over a builtin sequence) that `v00-baseline.mc` used before the
  `List`-based version replaced it.
* **`v13-reclets-lazy`** replaces `RecLetsEvalFList` with
  `RecLetsEvalFListLazy`, which is the same `List`-based encoding wrapped in a
  `lazy.mc` thunk so the bindings list is only built the first time the group's
  environment is extended.

## Regenerating

`v00`-`v05` and `v07`-`v13` are mechanical rewrites of `eval-fast.mc`. If the
baseline changes, regenerate them rather than patching each by hand — otherwise
a variant silently stops being "the baseline, one decision apart", which is the
only property that makes the comparison mean anything. `v06-unstaged.mc` is
written out by hand, since almost every `sem` changes shape.

`v00-baseline.mc` itself is regenerated by copying `eval-fast.mc`'s evaluator
body verbatim, minus any fragment `MExprEvalF` does not actually compose
(those are dormant experiments, not part of the baseline) — currently
`MatchEvalFLazy`, `MatchEvalFEagerPatConMap`, the alist `RecLetsEvalF`, and
`RecLetsEvalFListLazy`, which is exactly the set `v10`-`v13` each add back one
at a time.

The benchmarks in `../experiments` double as the correctness check: every
variant must produce the same exit code as every other on every program, which
`run-variants.sh` verifies on each run.
