# Miking

Miking (Meta vIKING) is a meta language system for creating embedded domain-specific and general-purpose languages. Miking is not a programming language, but rather a language system for
creating languages and generating efficient compilers.

## Getting started

Before you can use the Miking system, you need to install
[OCaml](https://ocaml.org/) and the
[OPAM](https://opam.ocaml.org/) package manager.

After the installation, you need to install the OCaml multicore compiler by
running the following:
```
opam update
opam switch create 4.12.0+domains --packages=ocaml-variants.4.12.0+domains --repositories=multicore=git+https://github.com/ocaml-multicore/multicore-opam.git,default
eval $(opam env)
```

After this, you need to install the `opam` packages `dune` and `linenoise` by
running the following:

```
opam install dune linenoise
```

Note that the `opam switch` command lets you have several OCaml installations on
your system. When using the Miking system, you need to use the `4.12.0+domains`
switch. Running `opam switch 4.12.0+domains` followed by `eval $(opam env)`
always takes you back to the correct switch.

To compile and run the test suite, go back to the Miking repository and execute:

```
make test
```

The Miking executable is available under `build/mi` after compiling the project. To run a hello world program, create a file `hello.mc` with the following code

```
mexpr print "Hello world!"
```

and then run it using command:

```
build/mi hello.mc
```

To help Miking find its standard library, you should define the
environment variable `MCORE_STDLIB` to be the path to `stdlib`,
for example by running the following:

    cd stdlib; export MCORE_STDLIB=`pwd`; cd ..;

To install the interpreter along with the standard library for the current
user, issue:

```
make install
```

This will install the interpreter to `$HOME/.local/bin` and the standard library to `$HOME/.local/lib/mcore/stdlib`, according to the [systemd file system hierarchy overview](https://www.freedesktop.org/software/systemd/man/file-hierarchy.html).

The Miking boot interpreter also features a simple REPL.
The REPL allows interactively executing fragments of MCore code.
Both toplevel definitions and expressions can be evaluated.

To start the REPL (assuming that the interpreter is installed in the path), run

```
boot repl
```

The following is an example interaction with the REPL.

```
Welcome to the MCore REPL!
Type :h for help or :q to quit.
>> let x = 5
>> let y = 10 in
 | addi x y
15
>>
```

## Editor Support

It is possible to write Miking code in any editor and compile it
via the command line. There are, however, editing modes for a
number of editors:

- [Emacs](https://github.com/miking-lang/miking-emacs)
- [Vim](https://github.com/miking-lang/miking-vim)
- [Sublime](https://github.com/miking-lang/miking-sublime-text)

If you create an editing mode of your own, please send a pull
request to update this list!

## MCore

MCore (Miking Core) is the core language of the Miking system. It is
based on a typed Lambda Calculus (Note: the type system is under
development, and the current implementation is untyped).

MCore consists of two parts:

* **MExpr** is an MCore expression. A Miking language is always translated into an MExpr, before it is further evaluated or compiled into machine code.

* **MLang** which is a language for defining and composing language fragments. MLang is formally translated into an MExpr.



## MExpr

One design objective of MExpr is to make the concrete syntax very close to the abstract syntax of the language. That is, no syntactic sugar is introduced to the concrete MCore syntax. The MExpr language is not intended to be a general-purpose programming language. Instead, the aim of MCore is to be a core language that other languages can translate into.

Nevertheless, to understand the Miking system, it is a good idea to learn to write basic programs directly as MCore expressions.

An MCore file `.mc` is in the end always translated into an MCore expression. If an MCore file contains `mexpr 5`, it means that the final expression of the program is value `5`. That is, `mexpr` states the start of the program and is followed by the actual MExpr of the program. If the keyword `mexpr` is left out of the file, a default mexpr unit value `()` is the resulting value.

### Unit Test Expressions

When writing MCore programs, it is typically done by writing explicit unit tests as part of the code. For instance

```
utest addi 1 2 with 3 in
()
```
checks that the addition of `1` and `2` is in fact `3`. To run the tests in an `.mc` file, run the `mi` command with argument `test` (assuming that you have now installed `mi` in your path):


```
mi run program.mc --test
```

Typically when you develop MCore programs, you do not use the `print` function. Instead, you write unit tests directly and then leave the units tests as is directly after your function. By doing so, you test your code, write regression tests, and document the informal semantics of your program directly. We strongly encourage you to develop your MCore programs this way.

### Intrinsics

MCore contains a number of built-in values (intrinsics) and
predefined functions and constants (part of the standard library).
For instance
```
mexpr
print "Hello"
```

uses the built-in function `print` which has the type `String -> Unit`, i.e., it prints a string and returns the unit type. In the rest of this section, we will leave out the `mexpr` keyword, and just write the MExpr itself.

The current documentation of intrinsics is implicit via code
containing `utest` expressions. Please see the following files:

* [Boolean intrinsics](test/mexpr/bool.mc)

* [Integer intrinsics](test/mexpr/int.mc)

* [Floating-point number intrinsics](test/mexpr/float.mc)

* [Strings intrinsics ](test/mexpr/string.mc)

* [Sequences intrinsics ](test/mexpr/seq.mc)

* [Side effect (printing, I/O, debugging etc.) intrinsics](test/mexpr/effects.mc)

* [Symbol intrinsics](test/mexpr/symbs.mc)

* [Reference intrinsics](test/mexpr/references.mc)

* [Random number generation intrinsics](test/mexpr/random.mc)

* [Time intrinsics](test/mexpr/time.mc)


### Let Expressions

Expressions can be given names using `let` expressions. For instance

```
let x = addi 1 2 in
x
```

introduces a new name `x`. The built-in function `addi` performs an addition between two integers. Note that MCore uses a call-by-value evaluation order, which means that expressions are evaluated into a value before they are applied to a function or substituted using a `let` expression. Hence, the expression `addi 1 2` is evaluated before it is substituted for `x` in the rest of the expression.


### Functions

Functions are always defined anonymously as lambda functions. If you would like to give a function a name, a `let` expression can be used. For instance, the following program defines a function `double` that doubles the value of its argument.

```
let double = lam x. muli x 2 in
utest double 5 with 10 in
()
```

Types can be expressed in MCore programs, but they are currently not checked. For instance, the `double` function can be written as

```
let double = lam x:Int. muli x 2 in
```

This means that `double` has type `Int -> Int`, which can also be expressed as part of the `let` expression.

```
let double : Int -> Int = lam x. muli x 2 in
```

A function with several parameters are expressed using currying, using nested lambda expressions. For instance, expression

```
let foo = lam x. lam y. addi x y in
utest foo 2 3 with 5 in
()
```
creates a function `foo` that takes two arguments.

A lambda can also be defined without a variable, e.g., `lam. e`, where
`e` is some expression representing the body of the function. Such
notation is useful if the actual variable is not used inside `e`. Note
that `lam. e` is syntactic sugar for a normal lambda `lam #var"". e`,
where the identifier of the variable name is the empty identifier.

### Sequencing

Sometimes an expression has a side effect and you are not interested
in the returned value. If that is the case, you can use the sequence
operator `;`. For instance, suppose you would like to print a value in
a function before it returns:

```
let foo = lam x.
  print x;
  x
```

The sequence operator `;` is not a construct of pure MExpr, but
syntactic sugar for a `let` construct. For instance, the pure version
(without syntactic sugar) of the program above is as follows:

```
let foo = lam x.
  let #var"" = print x in
  x
```

Note that a variable with an empty identifier is used in the `let` expression. Moreover, note that a `let` expression

```
let _ = foo x in ...
```

is syntactically not valid since `let` expressions always bind a value to a variable. Underscore `_` is a pattern and patterns are only allowed in `match` expressions.

### `if` Expressions

Conditional expressions can be expressed using `if` expressions. The program

```
let x = 5 in
let answer = if (lti x 10) then "yes" else "no" in
utest answer with "yes" in
()
```

checks if `x` is less than 10 (using the `lti` function with signature `Int -> Int -> Bool`). If it is true, the string `"yes"` is returned, else string `"no"` is returned.

Note that an `if` expression is not a construct in pure MExpr. It is syntactic sugar for a `match` expression. That is, expression

```
if x then e1 else e2
```

is translated into

```
match x with true then e1 else e2
```

### Recursion

A normal `let` expression cannot be used to define recursive functions. Instead, recursion can be defined using *recursive lets*, starting with the `recursive` keyword:

```
recursive
let fact = lam n.
  if eqi n 0
    then 1
    else muli n (fact (subi n 1))
in

utest fact 0 with 1 in
utest fact 4 with 24 in
()

```

Recursive lets can also be used to define mutually recursive functions. For instance:

```
recursive
let odd = lam n.
    if eqi n 1 then true
    else if lti n 1 then false
    else even (subi n 1)
let even = lam n.
    if eqi n 0 then true
    else if lti n 0 then false
    else odd (subi n 1)
in

utest odd 4 with false in
utest even 4 with true in
```


### Tuples

Product types can be expressed using tuples. An n-tuple is defined using syntax `(e_1, ..., e_n)` where `e_1` to `e_n` are MCore expressions. Extracting a value from a tuple (projection) is performed using an expression `e.n` where `e` is the expression that is evaluated into a tuple, and `n` is an integer number representing the index of an element in the tuple. The first index in a tuple is `0`.

For instance, in the MCore expression

```
let t = (addi 1 2, "hi", 80) in
utest t.0 with 3 in
utest t.1 with "hi" in
utest t.2 with 80 in
()
```
we create a 3-tuple `t` and project out its values. Note that the different elements of a tuple can have different types. In this case, tuple `t` has type `(Int, String, Int)`.

Singleton tuples are also supported: `(x,)` represents a tuple with `x` as its
only element.


### Records

Another more general form of product types are records. A record has
named fields that can have different types. For instance,

```
let r1 = {age = 42, name = "foobar"} in
```
defines a record of type `{age : int, name : string}`. The order of the fields does not matter:

```
utest r1 with {age = 42, name = "foobar"} in
utest r1 with {name = "foobar", age = 42} in
```

To project out a value, a dot notation may be used.

```
utest r1.age with 42 in
utest r1.name with "foobar" in
```

A record type is not just a general product type in MCore, it is the only
product type. That is, a tuple is just *syntactic sugar* for a record. This means that the compiler encodes a tuple as a record, where the names of the fields are numbers `0`, `1`, etc. Labels can internally be any kind of string. For strings that cannot be defined as a normal identifier, the label form `#label"x"`
can be used, where `x` is the string of the label.

The following example shows how a tuple is actually encoded as a
record.


```
utest ("foo",5) with {#label"0" = "foo", #label"1" = 5} in
```


### Data Types and `match` expressions

Sum types or variant types are constructed using `con` expressions (constructor expressions). In contrast to most other functional languages, the introduction of a new data type and the introduction of constructors are separated. For instance, the expression

```
type Tree in
con Node : (Tree,Tree) -> Tree in
con Leaf : (Int) -> Tree in
```

introduces a new data type `Tree` and defines two new constructors `Node` and `Leaf`. Constructor `Leaf` takes just one argument (an integer value for the leaf) and returns a tree, whereas the `Node` constructor takes a tuple with two trees as input and constructs a new tree node.

For instance, expression

```
let tree = Node(Node(Leaf 4, Leaf 2), Leaf 3) in
```

is a small tree named `tree`.

Assume now that we want to count the sum of the values of all leafs in a tree. We can then write a recursive function that performs the counting.

```
recursive
  let count = lam tree.
    match tree with Node t then
      let left = t.0 in
      let right = t.1 in
      addi (count left) (count right)
    else match tree with Leaf v then v
    else error "Unknown node"
in
```

The `match` expression inside the count function *deconstructs* data values by matching against a given constructor. For instance, the `match` expression

```
match tree with Node t then expr1 else expr2
```

matches the value after evaluating expression `tree` and checks if its outer most constructor is a `Node` constructor. If that is the case, the identifier `t` in expression `expr1` is bound to the tuple consisting of the node's two sub trees (recall the definition of the constructor `Node`). Finally, if we execute the test

```
utest count tree with 9 in ()
```

we can check that the function computes the result as intended.

### Pattern matching

In the previous match example, the `match` construct matched against
the constructor, but not against the actual data content. MExpr is
designed to be simple with few language construct, at the right level
of abstraction. If the abstraction level is too low, it is hard to
perform useful static analysis and code generation. As a consequence,
MExpr support *patterns* in `match` expressions. The `count` function
can be rewritten as

```
recursive
  let count = lam tree.
    match tree with Node(left,right) then
      addi (count left) (count right)
    else match tree with Leaf v then v
    else error "Unknown node"
in
```

where the match construct matches against pattern `Node(left,right)`,
where `left` and `right` are pattern variables.

Remember, however, that tuples are just syntactic sugar for records. Hence, match line

```
    match tree with Node(left,right) then
```
is equivalent to the following
```
    match tree with Node {#label"0"=left,#label"1"=right} then
```
where the pattern is a *record pattern*.

Pattern matching is the general form of deconstructing data in MExpr. Patterns can also be nested:

```
utest
  match {foo=7,bar={more="hello"}} with {foo=_,bar={more=str}} then str else ""
with "hello" in
```

Note also the use of *wildcard* patterns `_` (used in the `foo`
field), which matches any value.

Finally, MExpr also supports more advanced patterns, including `AND` patterns (using infix notation `&`)
```
utest match (1, 2) with (a, _) & b then (a, b) else (0, (0, 0)) with (1, (1, 2)) in
```

`OR` patterns (using infix notation `|`)
```
utest match K1 1 with K1 a | K2 a | K3 a then a else 0 with 1 in
```

and `NOT` patterns (using the prefix notation `!`)
```
utest match Some true with a & !(None ()) then a else Some false with Some true in
utest match None () with a & !(None ()) then a else Some false with Some false in

```

These are present to make it possible to translate order-dependent patterns to order-*in*dependent patterns. For example, in OCaml,

```ocaml
match (opt1, opt2) with
| (Some a, _) -> a
| (_, Some a) -> a
| (_, _) -> 1
```

is order-dependent; any change in pattern order changes which match-arm is executed. To express this in an order-independent manner we `&` every pattern with the inverse (`!`) of the union (`|`) of the previous patterns. If we pretent for a moment that OCaml supports `&` and `!` in patterns they could then be written as:

```ocaml
match (opt1, opt2) with
| (Some a, _) -> a
| (_, Some a) & !(Some a, _) -> a
| (_, _) & !((Some a, _) | (_, Some a))-> 1
```

The order can now be changed freely without affecting the semantics. In practice `&` and `!` will probably rarely be used in manually written code, while `|` is rather more useful.

### Sequences

An MCore sequence is constructed using syntax `[e_1, ..., e_n]`. All elements in a sequence must have the same type. For instance, an expression

```
[1,3,6,7,22,3]
```
has type `[Int]` whereas and expression

```
["this", "is", "a", "test"]
```

has type `[String]`.

A string itself is actually a sequence of characters. Hence,

```
utest "foo" with ['f','o','o'] in ()
```

is correct. This means that the type `String` is just an abbreviation for the sequence type `[Char]`.

There are several operations defined for sequences, for instance, the `concat` function concatenates two sequences

```
utest concat [1,3,5] [7,9] with [1,3,5,7,9] in ()
```

or the `get` function picks out the nth element of a sequence

```
utest get [3,5,8,9] 2 with 8 in ()
```

It is also possible to pattern match on sequences, to either extract the *tail* of a sequence, if the first part matches

```
utest match "foobar" with "fo" ++ rest then rest else ""
with "obar" in
```

or the *head* of a sequence if the last part matches:

```
utest match "foobar" with first ++ "bar" then first else ""
with "foo" in
```

It is even possible to extract the middle of a sequence, if the head and the tail matches:

```
utest match "foobar" with "fo" ++ mid ++ "ar" then mid else ""
with "ob" in
```

Again, matching can be combined and nested:

```
utest match (1,[["a","b"],["c"]],76) with (1,b++[["c"]],76) then b else []
with [["a","b"]] in
```

### Tensors
Tensors are mutable data structures and can be of up to rank 16. The index
of an element is represented as a sequence of integers.

We construct tensors using `tensorCreateDense shape f`, where `shape` is a sequence
denoting the shape of the tensor and `f` is a function taking an index as an
argument and returning the element at that index.

We can construct a zero-order tensor with value `'a'` as
```
let t0 = tensorCreateDense [] (lam _. 'a') in
utest tensorRank t0 with 0 in
utest tensorShape t0 with [] in
```

We can access and mutate elements in a tensor using
```
utest tensorSetExn t0 [] 'b' with () in
utest tensorGetExn t0 [] with 'b' in
```

We can construct a rank 1 tensor (i.e. vector) as
```
let t1 = tensorCreateDense [9] (lam i. addi (get i 0) 1) in
utest tensorToSeqExn t1 with [1, 2, 3, 4, 5, 6, 7, 8, 9] in
```
where `tensorToSeqExn` is defined in `tensor.mc`.

We can reshape our rank 1 tensor into a rank 2 tensor (i.e. a matrix).
```
let t2 = tensorReshapeExn t1 [3, 3] in
```

Reshape does no copying and the data is shared between `t1` and `t2`
```
let _ = tensorSetExn t2 [0, 0] 2 in
utest tensorGetExn t1 [0] with 2 in
```

We can slice the second row from `t2` as
```
let r2 = tensorSliceExn t2 [1] in
utest tensorToSeqExn r2 with [4, 5, 6] in
```

Slicing reduces the rank of the tensor
```
utest tensorRank r2 with 1 in
```

We can slice multiple dimensions at once
```
let e = tensorSliceExn t2 [1, 1] in
utest tensorGetExn e [] with 5 in
utest tensorRank e with 0 in
```

A slice shares data with the original tensor and no copying of data is done.
```
let _ = tensorFill r2 0 in
utest tensorToSeqExn t1 with [2, 2, 3, 0, 0, 0, 7, 8, 9] in
```
where we use `tensorFill` from `tensor.mc`.

We can get a subset of the rows of t2 by restricting its 0th dimension.
```
let s1 = tensorSubExn t2 1 2 in
utest tensorShape s1 with [2, 3] in
utest tensorToSeqExn (tensorReshapeExn s1 [6]) with [0, 0, 0, 7, 8, 9] in
```

### References

A mutable reference to an MExpr value can be created with the `ref` operator. For instance

```
let r = ref 3 in
```

allocates a reference to a cell in memory with an initial value `3`, and binds
the reference to the variable `r`.

The `deref` operator is used for dereferencing, that is, to read the value that
a reference points to:

```
let r = ref 3 in
utest deref r with 3 in ()
```

The value that a reference points to can be modified using the `modref` operator:

```
let r = ref 3 in
let _ = modref r 4 in
utest deref r with 4 in ()
```

Note that the return value of `modref` is an MExpr unit value.

It is possible have aliases for the same memory cell by binding several
variables to the same reference. As an example, in the program

```
let r1 = ref "A" in
let r2 = r1 in
let _ = modref r2 "B" in
utest deref r1 with "B" in ()
```

the change made to the referenced value via the variable `r2` is visible when
dereferencing the reference via the variable `r1`.

### Parallel Programming
Miking has support for shared-memory parallelism using atomic operations and
threads running on multiple cores.

The parallel programming primitives consist of atomic references and functions
for creating and synchronizing threads. In addition to the examples below, more
documentation can be found in the [multicore test
suite](test/multicore/multicore.mc).

#### Atomic References

Atomic references are similar to ordinary references, except that operations
performed on them are *atomic*, which means that no other execution thread can
interfere with the result. In other words, they are safe to use in
multi-threaded execution.

`atomicMake` creates a new atomic reference and gives it an initial value. The
value of the atomic reference can be read by `atomicGet`:

```
let a = atomicMake 0 in
utest atomicGet a with 0 in
```

`atomicCAS a oldVal newVal` performs an atomic compare-and-set, that is, it only
updates the value of `a` to `newVal` if the current value is identical to
`oldVal`, and then returns a Boolean representing if the update was successful
or not:

```
utest atomicCAS a 0 1 with true in
utest atomicCAS a 42 3 with false in
utest atomicGet a with 1 in
```

The compare-and-set operation is currently supported for integer atomic
references only.

To unconditionally set the value of an atomic reference, we can use
`atomicExchange`, which also returns the old value of the reference:

```
utest atomicExchange a 2 with 1 in
```

Finally, for integer references, we can use `atomicFetchAndAdd` to increase or
decrease the value of the reference. The function returns the old value of the
reference:

```
utest atomicFetchAndAdd a 1 with 2 in
-- Current value is now 3
utest atomicFetchAndAdd a (subi 0 45) with 3 in
-- Current value is now -42
```

#### Multi-Threaded Execution

The following example program spawns 10 threads that compete for printing their
IDs:

```
include "string.mc"
mexpr
let place = atomicMake 1 in
let threads = create 10 (lam. threadSpawn (lam.
  printLn (join
    [int2string (atomicFetchAndAdd place 1)
    , ": thread ID "
    , int2string (threadID2int (threadSelf ()))
    ]))
) in
map threadJoin threads
```

where `threadSpawn` takes a function of type `Unit -> a` as argument,
`threadSelf` returns the ID of the current thread, and `threadID2int` converts a
thread ID to a unique integer. Note that `threadJoin` must be called once for
each call to `threadSpawn`. The output of the above program might be:

```
1: thread ID 1
2: thread ID 2
3: thread ID 129
4: thread ID 130
5: thread ID 3
6: thread ID 257
7: thread ID 258
8: thread ID 131
9: thread ID 385
10: thread ID 386
```

However, the values and order of the thread IDs might be different over
different runs.

To control the execution order of threads, some form of thread synchronization
is necessary. This can be done either using atomic references, or using the
functions `threadCriticalSection`, `threadWait` and `threadNotify`, or both.
In the following example:

```
let inCriticalSection = atomicMake false in
let afterWait = atomicMake false in

let t = threadSpawn (lam.
  threadCriticalSection (
    lam.
      atomicExchange inCriticalSection true;
      threadWait ();
      atomicExchange afterWait true
  )
) in
```

the thread `t` enters a critical section, where it first atomically sets the
`inCriticalSection` flag to true, before calling `threadWait`, which will block
the execution until another thread calls `threadNotify`. In the following, the
main thread first waits for `t` to set the `inCriticalSection` flag, before
making a call to `threadNotify`:

```
recursive let waitForFlag = lam flag.
  match atomicGet flag with true then ()
  else waitForFlag flag
in
waitForFlag inCriticalSection;
threadNotify (threadGetID t);
```

The `threadNotify` will block the execution of the main thread until `t` has
finished its critical section, which means that we know that the flag
`afterWait` must now be true:

```
utest atomicGet afterWait with true in
-- Don't forget to clean up!
threadJoin t;
```

## MLang

MLang is a superset of MExpr, and is used to define and compose
reusable language fragments. It also supports top-level
definitions and simple file inclusion. The definitions can be
translated into pure MExpr definitions, and can be run as any
other MExpr programs.

### Top-Level Definitions and Includes

Values, types, and data constructors can be defined top-level,
before the `mexpr` keyword of an MCore program. The syntax is
identical to that of the corresponding MExpr definitions, without
the trailing `in`:

```
let id = lam x. x
type T
con Foo : Int -> T

mexpr

utest id (Foo 42) with Foo 42 in
()
```

The translation into MExpr is straightforward: the definitions are
simply moved into the beginning of the `mexpr` program. The
usefulness of top-level definitions becomes more apparent when
adding included files. A file can be included using the syntax

```
include "path/to/prog.mc"
```

before any top-level definitions in a
file. The string is a file path relative to the file that contains
the `include`. If the environment variable `MCORE_STDLIB` is
defined, its value is used as a fallback path to search from if
the file is not found relative to the original file. Files are
included transitively in a depth-first fashion, and files that are
included from several files are only included once. File
inclusions that form a loop are not allowed.

Including a file is equivalent to inserting all the top-level
definitions of that file. There are no namespaces and no
disambiguation; if a name defined in an included file is shadowed
in the including file, the included definition becomes
unavailable.


### Language Fragments

A language fragment contains definitions of (abstract) syntax, and
semantics ("interpreters") for that fragment. Any number of
language fragments can be defined before the `mexpr` keyword in an
MCore program. For example, here is a language fragment for simple
arithmetics:

```
lang Arith
  syn Expr =
  | Num Int
  | Add (Expr, Expr)

  sem eval =
  | Num n -> Num n
  | Add (e1,e2) ->
    match eval e1 with Num n1 then
      match eval e2 with Num n2 then
        Num (addi n1 n2)
      else error "Not a number"
    else error "Not a number"
end
```

The fragment defines a syntactic form with two cases called
`Expr`, and an interpreter called `eval`. An interpreter in MLang
is a function that is always defined by cases over its last
argument (here, `eval` takes only a single argument). The body of
a case is a regular MExpr term, which has access to the name of
the value (if any) carried by the current syntactic form.

In the main MExpr program, a language fragment can be opened by
a `use` expression:

```
mexpr
use Arith in
utest eval (Add (Num 2, Num 3)) with Num 5 in
()
```

A `use` is translated into a series of MExpr definitions that
match the syntax and semantics of the specified language fragment.

An important feature of language fragments is that they can be
composed to form new language fragments. As an example, we might
want to extend our arithmetics language with booleans and `if`
expressions:

```
lang MyBool
  syn Expr =
  | True()
  | False()
  | If (Expr, Expr, Expr)

  sem eval =
  | True() -> True()
  | False() -> False()
  | If(cnd,thn,els) ->
    let cndVal = eval cnd in
    match cndVal with True() then eval thn
    else match cndVal with False() then eval els
    else error "Not a boolean"
end

lang ArithBool = Arith + MyBool

mexpr
use ArithBool in
utest eval (Add (If (False(), Num 0, Num 5), Num 2)) with Num 7 in
()
```

The language fragment `ArithBool` is indistinguishable from a
language fragment with all the syntactic and semantic cases of
`Arith` and `MyBool` merged. If we wanted, we could have added new
cases to the language composition as well, and refer to the syntax
and semantics of the fragments being composed:

```
lang ArithBool = Arith + MyBool
  syn Expr =
  | IsZero Expr

  sem eval =
  | IsZero e ->
    match eval e with Num n then
      if eqi n 0 then True() else False()
    else
      error "Not a number"
end
```

<!--
NOTE(?,?): The following text needs to be updated since we now have
nested patterns, even for MLang.


### Designing for Extensibility

The language fragments in the previous sections can be reused when
adding new syntactic forms to our language. However, we are not
able to extend the semantics of the existing syntactic forms. For
example, we might want to overload the `Add` case so that it can
use expressions other than integers. In order to cater to such
extensions, we have to design our language fragments with this in
mind. Below is an example of how we might go about it.

We start by defining a language fragment that only defines the
general (abstract) syntax and semantics of addition. We delegate
the last step of evaluation to another semantic definition
`performAdd`, which currently can only define one case: the
failure case.

```
lang Addition
  syn Expr =
  | Add (Expr, Expr)

  sem eval =
  | Add t ->
    let e1 = t.0 in
    let e2 = t.1 in
    performAdd (eval e1) (eval e2)

  sem performAdd (v1 : Expr) =
  | _ -> error "Cannot perform addition"
end
```

Note that even though `performAdd` has a catch-all case, it can be
extended with new cases in other language fragments; patterns are
matched _from most to least specific_, not in the order they are
defined (as is common in most functional languages). We can now
define addition for integers and floats in two language fragments,
and compose them together to form a language that supports
addition for both syntactic forms. Note that we can also reuse the
language fragment for booleans from before:

```
lang Integer = Addition
  syn Expr =
  | Integer Int

  sem eval =
  | Integer n -> Integer n

  sem performAdd (v1 : Expr) =
  | Integer n2 ->
    match v1 with Integer n1
    then Integer (addi n1 n2)
    else error "Not an integer"
end

lang Real = Addition
  syn Expr =
  | Real Float

  sem eval =
  | Real r -> Real r

  sem performAdd (v1 : Expr) =
  | Real r2 ->
    match v1 with Real r1
    then Real (addf r1 r2)
    else error "Not a real"
end

lang ArithReal = Integer + Real + Bool

mexpr

use ArithReal in
utest eval (Add (Integer 2, Integer 3)) with Integer 5 in
utest eval (Add (If (True, Real 4.0, Real 0.0), Real 3.0)) with Real 7.0 in
()
```

-->

### Known Issues/Future Work
<!--
* Pattern matching in interpreters is shallow, which sometimes
requires defining interpreters in multiple "layers" to maintain
extensibility.

* Iterpreters are always defined on pattern matching on a single
parameter, which also forces the programmer to define several
interpreters to achieve the same thing.
-->

* Name binding in language definitions is dynamic in where the
  language is used, meaning that shadowing can change behavior in
  unexpected ways (a type system would address this to some
  extent).
* There are cases where it would be useful to `use` language
  fragments top-level, for example when defining top-level
  functions that use datatypes defined in language fragments.
* The intended rules of interpreter composition are as follows:
  - If a language defines a case c1 that overlaps with a case c2
    from a language being extended, c1 takes precedence (cf.
    overriding in inheritance).
  - If a language extends two languages which both define the same
    case for an interpreter, the extending language _must_ provide
    an overriding case for that interpreter.


## Externals (builtin)

As part of the experimental setup of Miking, we currently support a way
to use external libraries without interfering with the development of
Miking that does not need these external dependencies.

### Python
Another optional feature is Python intrinsics, which allow calling Python code
from MCore. To build the project with Python integration you need to have
[Python 3](https://www.python.org) installed on your system. You will also need to install any Python libraries you want to use (for example using pip).

In addition, you need the [pyml](https://github.com/thierry-martinez/pyml) OCaml Python bindings, available via `opam`:

```
opam install pyml
```

`mi` will automatically be compiled with Python support when the `pyml` package is installed.

NOTE: Currently, there seems to be a problem with the current OPAM bindings with the multicore switch. If the above command fails, try to run the following and then install `pyml` again:

```
opam pin stdcompat 15
```

To run the Python-specific test suite, set the `MI_TEST_PYTHON` variable before running `make test`:

```
MI_TEST_PYTHON=1 make test
```

To install for the current user, run `make install` as usual.

#### Usage

The following example shows how to use the intrinsics to sort a sequence using
Python's builtin `sorted` function.

```ocaml
let builtins = pyimport "builtins"

let x = [5.,4.5,4.,1.,1.5]
let y = pycall builtins "sorted" (x,)
let x_sorted = pyconvert y
```

`pycall` is the main piece of the Python intrinsics: in the example above,
it is used to call the function `sorted` from the `builtins` module, imported
with the `pyimport` intrinsic. As the example shows, arguments are
passed to the `pycall` intrinsic using tuples (remember that `(x,)` is a
singleton tuple containing `x`). The result of a `pycall` (`y` in the example
above) is a Python value, which can either be passed to other Python functions,
or converted back to an MCore sequence using the `pyconvert` builtin.

`pycall` can also be used to call methods of objects by passing an object
instead of a module as the first argument. For example, the following code
will invoke the `count` method of a list:

```ocaml
let builtins = pyimport "builtins"

let pylist = pycall builtins "list" ([1,1,2],)
let ones = pyconvert (pycall pylist "count" (1,))
```

In the examples above, we use the `builtins` module to access Python's builtins.
Other modules can also be imported as long as they are available in the Python
path: for instance, it is perfectly possible to import `numpy` or `matplotlib`,
assuming that they are installed.

The following example shows how a numpy `nparray` can be created and converted
to an MCore sequence. The key here is to use numpy's `tolist` method first,
since conversion directly from `nparray` is not supported.

```ocaml
let rnd = pyimport "numpy.random"

let nparray = pycall rnd "normal" (0., 0.1, 10)
let mc_seq = pyconvert (pycall nparray "tolist" ())
```

In the next example, we use `matplotlib` to produce a plot; this works in
exactly the same way as in a regular Python program.

```ocaml
let plt = pyimport "matplotlib.pyplot"
let np = pyimport "numpy"

let x = pycall np "arange" (0, 4, 0.1)
let y = pycall np "cos" (x,)
let _ = pycall plt "plot" (x, y)
let _ = pycall plt "show" ()
```

#### Conversion between MCore and Python

When calling a Python function using the `pycall` builtin, the arguments will be
automatically converted from MCore values to Python values. Similarly, the
opposite conversion is performed when using `pyconvert` on the result of a
`pycall`. This section explains the details of these conversions.

##### From MCore to Python

| MCore type      | Python type |
|:--------------- |:----------- |
| Bool            | bool        |
| Int             | int         |
| Char            | N/A         |
| Float           | float       |
| [Char] (String) | str         |
| [a]             | List        |
| Unit            | None        |
| Record          | Dict        |
| Tuple (Record)  | Tuple       |
| other           | N/A         |

##### From Python to MCore

| Python type | MCore type      |
|:----------- |:--------------- |
| bool        | Bool            |
| int         | Int             |
| long        | Int             |
| float       | Float           |
| str         | [Char] (String) |
| List        | [a]             |
| None        | Unit            |
| Dict        | Record          |
| Tuple       | Tuple (Record)  |
| other       | N/A             |

## Compiling to OCaml
The standard library contains functions for compiling and running `mexpr`
programs targeting OCaml. See the implementation in
[stdlib/ocaml](stdlib/ocaml). This library requires the python intrinsics and
that the `boot` package is installed globally for your user. To do the latter,
run

```
dune install
```

after building miking with python intrinsics support.

## Externals

Externals allows you to interact with code in the compilation target language
from miking. Currently, externals are only available in compiled code and are
in an early stage of development. The example below only covers the case where
OCaml is the target language.

You can find an example of externals definitions in
[stdlib/ext/math-ext.mc](stdlib/ext/math-ext.mc) and
[stdlib/ext/math-ext.ext-ocaml.mc](stdlib/ext/math-ext.ext-ocaml.mc).

For the sake of this example, lets say we want to define the exponential
function and that miking targeting OCaml should use `Float.exp` from OCaml's
standard library for its implementation.

We first define the external in a file under [stdlib/ext](stdlib/ext), let's
say [stdlib/ext/math-ext.mc](stdlib/ext/math-ext.mc), as

```
external externalExp : Float -> Float
```

which makes an external value `externalExp` of type `Float -> Float` available
at the top-level. The corresponding MCore syntax is:

```
external ident : Type in expr
```

If the external has side-effects it should be annotated with a `!` after the
identifier, e.g.

```
external print ! : String -> ()
```

Each external identifier can only be defined once and externals cannot be
partially applied.


As a temporary solution, the next step is to supply a list of implementation for
our external in the language we target for compilation (in this case OCaml). We
do this by creating a file
[stdlib/ext/math-ext.ext-ocaml.mc](stdlib/ext/math-ext.ext-ocaml.mc)
and in it we define a map from external
identifiers to a list of implementations as follows:

```
include "map.mc"
include "ocaml/ast.mc"

let mathExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("externalExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ , libraries = [] }
    ])
  ]
```

This map associates the `externalExp` external to a list of implementations,
which here only has one element, namely the function `Float.exp` from OCaml's
standard library. The field `ty` encode the OCaml type of this value (see
[stdlib/ocaml/ast.mc](stdlib/ocaml/ast.mc)), which is needed to convert values
between miking and OCaml. In the case where you have multiple implementations,
the compiler will try to pick the implementation which gives the least amount of
overhead when converting to and from OCaml values. The `libraries` field list
libraries that are needed to call this function. In this case none is needed
since it is part of the standard library. If let's say we wanted to use
`Float.exp` from a library `foo`, then we should instead have the field `libraries =
["foo"]`. Finally, we need to add `mathExtMap` to `globalExternalImplsMap` in
[stdlib/ocaml/external-includes.mc](stdlib/ocaml/external-includes.mc).

If you use more complicated data-structures, please consult
[stdlib/ext/ext-test.mc](stdlib/ext/ext-test.mc) and
[stdlib/ext/ext-test.ext-ocaml.mc](stdlib/ext/ext-test.ext-ocaml.mc)
(and possibly extend [stdlib/ocaml/external.mc](stdlib/ocaml/external.mc)), to
see how these are converted to and from OCaml. As of now, there is no overhead
when converting between integers, floats, bools, chars, and tuples of these as
well as arrow types of these.

### Sundials

A more involved example on the use of externals is an interface to the
[Sundials](https://computing.llnl.gov/projects/sundials) numerical DAE solver.
You find the implementation in
[stdlib/sundials/sundials.mc](stdlib/sundials/sundials.mc) and
[stdlib/sundials/sundials.ext-ocaml.mc](stdlib/sundials/sundials.ext-ocaml.mc).
Note that these externals depends on the library `sundialsml`.


Installing this library involves first installing the Sundials C library. On
`ubuntu 20.04` you can do this by:

```
sudo apt-get install libsundials-dev
```

On `macOS`, using Homebrew, you instead do:

```
brew install sundials
```

Then install the ocaml bindings
[SundialsML](https://inria-parkas.github.io/sundialsml/) via `opam`

```
opam install sundialsml
```

Currently, this library cannot be installed on the multi-core switch but you
instead have to use another opam switch, e.g.

```
opam switch 4.12.0
```

After this you have to rebuild the compiler, e.g.

```
make clean
make
```

To run the sundials-specific test suite, use the command:

```
make test-sundials
```

To install for the current user, run `make install` as usual.

## Contributing

1. Before making a pull request please make sure that all tests pass. Run
appropriate tests as described above.

2. Make sure you follow the conventions declared in the
[wiki](https://github.com/miking-lang/miking/wiki/Conventions).

3. We use [ocamlformat](https://github.com/ocaml-ppx/ocamlformat) to
automatically format ocaml source code.

###  Setup and use `ocamlformat`

We are currently using this package at version `0.16.0`. To pin and/or install
the package at this version using `opam` do
```
opam pin ocamlformat 0.16.0
```
Then you can then run `dune build @fmt` to see a
diff between your code and the formatted code. To promote the changes run `dune
promote`. To do these two steps in one run `dune build @fmt --auto-promote`. If
you want to, you can run `ocamlformat` in watch mode to continuously format the
source as you work on it with the command `dune build @fmt --auto-promote -w`.
You can also find instructions for tighter editor integration at *ocamlformat's*
GitHub page.

For convenience, `make lint` will run `dune build @fmt` and `make fix` will run
`dune build @fmt --auto-promote`.

### Git Blame

Since automatic code formatting commits will obscure `git blame` we maintain a
file  [.git-blame-ignore-revs](.git-blame-ignore-revs) that will contain the
commit hashes of code formatting commits. We can then run `git blame`, ignoring
these commits as:

```
git blame <file(s)> --ignore-revs-file .git-blame-ignore-revs
```

To make this setting persistent you can configure git like this:

```
git config blame.ignoreRevsFile .git-blame-ignore-revs
```

These instructions are adapted from
[https://github.com/psf/black](https://github.com/psf/black). See
[https://git-scm.com/docs/git-blame#Documentation/git-blame.txt---ignore-revltrevgt](https://git-scm.com/docs/git-blame#Documentation/git-blame.txt---ignore-revltrevgt)
for documentation on the `--ignore-revs-file` option.


## MIT License
Miking is licensed under the MIT license.

Copyright 2017-2019 David Broman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
