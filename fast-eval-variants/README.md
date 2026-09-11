# `eval-fast.mc` design variants

Nine standalone copies of `src/stdlib/mexpr/eval-fast.mc`, each changing
**exactly one** design decision and leaving everything else alone, so that the
difference between a variant and the baseline measures that one decision rather
than a combination.

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

  Two accommodations it needs, neither of which affects what is measured:
  `lowerAll` emits a couple of discarded `let` bindings with no name at all, so
  `LetEvalF` evaluates those for effect and binds nothing; and it builds an
  error message with `print` on the fallthrough of every lowered match, so the
  variant carries an `IOEvalF` fragment. Nothing reaches that path in a program
  whose matches are exhaustive, but `mkEvalF` compiles the whole AST up front,
  so the constant still has to resolve.

## Regenerating

`v00`-`v05` and `v07`-`v09` are mechanical rewrites of `eval-fast.mc`. If the
baseline changes, regenerate them rather than patching each by hand — otherwise
a variant silently stops being "the baseline, one decision apart", which is the
only property that makes the comparison mean anything. `v06-unstaged.mc` is
written out by hand, since almost every `sem` changes shape.

The benchmarks in `../experiments` double as the correctness check: every
variant must produce the same exit code as every other on every program, which
`run-variants.sh` verifies on each run.
