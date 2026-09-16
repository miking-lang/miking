# ECMAScript backend

Note that ECMAScript is the specification and JavaScript is an implementation.
They are commonly used interchangeably.

## Design

The most prominent design requirement is that the generated code should be readable.
That means no waterfall created by in-chains.
The code should be flattened to sequential statements.

The backend should be usable for bootstrapping the compiler,
and for running in the browser.

Sine a compiled version of the compiler is to be checked into the repository,
the output from the backend should be stable.

The backend is designed to generate 100% generic code.
The generated code does not make any assumptions about the host runtime that it is running on.
This is solved by having the entire program be wrapped in a exported function that takes a
single argument that is a environment with host specific implementations.
An example host environment for nodejs can be found in [hosts/node.mjs](./hosts/node.mjs).
There is also a provided script [misc/scripts/es-node-run.mjs](../../../misc/scripts/es-node-run.mjs).
That will run a program with the default nodejs environment.

The backend targets the mlang-pipeline only since it does not implement boot specific intrinsics.

## Readability

A simple example program:

```ocaml
let a = 1 in 
let b = 2 in 
let c = addi a b in 
dprint c
```

Should compile to:

```javascript
export default function main(env) {
  const a = 1;
  const b = 2;
  const c = a + b;
  env.dprint(c);
}
```

Named bindings of lambdas should create a single function:


```ocaml
let add = lam x. lam y. addi x y in
let inc = add 1 in
let apply = lam f. lam v. f v in
let twice = lam f. lam v. f (f v) in
let alias = add in

dprint (add 2 3);
dprint (inc 41);
dprint (apply (add 10) 5);
dprint (twice inc 0);
dprint (alias 20 22);
dprint ((lam x. muli x x) 7);
```

But partial applications should still work:

```javascript
function add(x, y) {
  return x + y;
}
const inc = a => add(1, a);
function apply(f, v) {
  return f(v);
}
function twice(f, v) {
  return f(f(v));
}
env.dprint(add(2, 3));
env.dprint(inc(41));
env.dprint(apply(a => add(10, a), 5));
env.dprint(twice(inc, 0));
env.dprint(add(20, 22));
env.dprint((x => x * x)(7));
```

### Cleanup

Unlike the OCaml backend the output from the ECMAScript backend is not passed to another
compiler that runs additional optimization steps.
Therefore some of these steps needs to be performed by this backend in order to retain readability.

Some things that needs to be done are:

* Allocate variable names, only add numeric suffix in case of duplication.

* The mlang-pipeline adds let bindings for all intrinsics at the top of the program,
  this turns all uses into function calls that the OCaml compiler would optimize away.
  This backend needs to do this manually.

* The input AST contains a lot of temporary variables that needs to be removed or inlined.


## Tail calls

JavaScript engines do not eliminate tail calls, so a tail call would grow the stack.

A new mutual function is created that takes a tag parameter and runs in a loop.

```ocaml
recursive
  let even = lam x. if eqi x 0 then true else odd (subi x 1)
  let odd = lam x. if eqi x 1 then true else even (subi x 1)
in
dprint (even 4000000)
```

```javascript
function even(x) {
  return even_odd(0, x, undefined);
}
function odd(x) {
  return even_odd(1, undefined, x);
}
function even_odd(tag, x, x_1) {
  while (true) {
    if (tag === 0) {
      if (x === 0) {
        return true;
      } else {
        x_1 = x - 1;
        tag = 1;
        continue;
      }
    } else if (tag === 1) {
      if (x_1 === 1) {
        return true;
      } else {
        x = x_1 - 1;
        tag = 0;
        continue;
      }
    }
  }
}
env.dprint(even(4000000));
```

Pattern lowering hides tail calls behind join points: a local binding whose body does
nothing but call back into the function it sits in.
Such a binding is substituted back at its call sites, which costs nothing
and exposes the direct tail call.

## Data representation

| MExpr | ECMAScript |
| --- | --- |
| `Int` | `number`, this is a 64-bit float |
| `Float` | `number` |
| `Bool` | `true` / `false` |
| `Char` | one-character `string` |
| `[a]` | `$Seq`, custom implementation of a rope |
| Record | plain object |
| Tuple | plain object with numeric keys |
| Unit `()` | `undefined` |
| `Con x` | class instance, `new Some(x)` |
| `Ref` | `{v: x}` |

Noteworthy things are

* Integers are represented by 64-bit floats.
  This is common in JavaScript land.
  Where is also `BigInt` which is a variable sized integer,
  it was not chosen since it would make every integer heap allocated.

* Sequences are **not** JavaScript arrays, since the complexity differs for many operations.
  `$Seq` is a custom implementation of a rope.

* Strings are **not** plain JavaScript strings, whey are a sequence of chars.
  However when the program calls and returns from JavaScript land (environment functions),
  strings are marshalled to and from plan JavaScript strings.

* Tuples are just records, but they are also marshalled (to arrays) when passed to and from
  environment functions.

* Unit is `undefined` as opposed to a empty object.
  This is done for readability since `undefined` is implicit in JavaScript.

* Constructors are Sub-classes of a base class (the type).
  This is also for readability. Ex: `Bar extends Foo {...}` and `a instanceof Bar`.
