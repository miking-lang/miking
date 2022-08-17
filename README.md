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

To compile the project, go back to the Miking repository and execute:

```
make
```

This creates two binaries in the `build` directory: `build/boot` and
`build/mi`. `build/boot` is the bootstrap interpreter, and `build/mi`
is the main Miking executable, containing both an interpreter and a
compiler. You will mainly be using `mi`, but `boot` provides a few
features not yet available in the main executable, such as a REPL.

To run tests checking that everything has been installed correctly,
use

```
make test
```

Alternatively, you can use `make test-all` to run the full test suite. Beware
that this may take some time. Alternatively you can use `make
test-all-prune-utests` which will exclude tests whose external dependencies are
not met on the current system (with the exception of `pyml`).

To run a hello world program, create a file `hello.mc` with the following code,

```
mexpr print "Hello world!\n"
```

and then run it using the command:

```
build/mi hello.mc
```

To help Miking find its standard library, you should define the
environment variable `MCORE_STDLIB` to be the path to `stdlib`,
for example by running the following:

    cd stdlib; export MCORE_STDLIB=`pwd`; cd ..;

To install the compiler along with the standard library for the current
user, issue:

```
make install
```

This will install `mi` to `$HOME/.local/bin` and the standard library to `$HOME/.local/lib/mcore/stdlib`, according to the [systemd file system hierarchy overview](https://www.freedesktop.org/software/systemd/man/file-hierarchy.html). If `MCORE_STDLIB` is unset, Miking will look in this installation folder as its default library location.

Conversely, to uninstall, issue:

```
make uninstall
```

### The REPL
The Miking bootstrap interpreter features a simple REPL, which lets
you interactively execute fragments of MCore code. Both toplevel
definitions and expressions can be evaluated.

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

In the end, an MCore file `.mc` is always translated into an MCore expression. If an MCore file contains `mexpr 5`, it means that the final expression of the program is value `5`. That is, `mexpr` states the start of the program and is followed by the actual MExpr of the program. If the keyword `mexpr` is left out of the file, a default mexpr unit value `()` is the resulting value.

### Unit Test Expressions

When writing MCore programs, it is typically done by writing explicit unit tests as part of the code. For instance

```
mexpr
utest addi 1 2 with 3 in
()
```
checks that the addition of `1` and `2` is in fact `3`. To run the tests in an `.mc` file, run the `mi` command with argument `test` (assuming that you have now installed `mi` in your path):


```
mi run program.mc --test
```

Typically when you develop MCore programs, you do not use the `print` function. Instead, you write unit tests directly and then leave the units tests as is directly after your function. By doing so, you test your code, write regression tests, and document the informal semantics of your program directly. We strongly encourage you to develop your MCore programs this way.

In the rest of this document, we omit the `mexpr` keyword for brevity, and just write the MExpr itself. Remember to add it as appropriate when trying the various examples.

### Intrinsics

MCore contains a number of built-in values (intrinsics) and
predefined functions and constants (part of the standard library).
For instance,

```
print "Hello\n"
```

uses the built-in function `print` which has the type `String -> ()`, i.e., it prints a string and returns the unit type.

The current documentation of intrinsics is implicit via code
containing `utest` expressions. Please see the following files:

* [Boolean intrinsics](test/mexpr/bool-test.mc)

* [Integer intrinsics](test/mexpr/int-test.mc)

* [Floating-point number intrinsics](test/mexpr/float-test.mc)

* [Strings intrinsics ](test/mexpr/string-test.mc)

* [Sequences intrinsics ](test/mexpr/seq-test.mc)

* [Side effect (printing, I/O, debugging etc.) intrinsics](test/mexpr/effects.mc)

* [Symbol intrinsics](test/mexpr/symbs.mc)

* [Reference intrinsics](test/mexpr/references.mc)

* [Random number generation intrinsics](test/mexpr/random-test.mc)

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

Note that an `if` expression is not a construct in pure MExpr. It is syntactic sugar for a `match` expression. That is, the expression

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
()
```

A record type is not just a general product type in MCore, it is the only
product type. That is, a tuple is just *syntactic sugar* for a record. This means that the compiler encodes a tuple as a record, where the names of the fields are numbers `0`, `1`, etc. Labels can internally be any kind of string. For strings that cannot be defined as a normal identifier, the label form `#label"x"`
can be used, where `x` is the string of the label.

The following example shows how a tuple is actually encoded as a
record.


```
utest ("foo",5) with {#label"0" = "foo", #label"1" = 5} in ()
```


### Data Types and `match` expressions

Sum types or variant types are constructed using `con` expressions (constructor expressions). In contrast to most other functional languages, the introduction of a new data type and the introduction of constructors are separated. For instance, the expression

```
type Tree in
con Node : (Tree,Tree) -> Tree in
con Leaf : (Int) -> Tree in
```

introduces a new data type `Tree` and defines two new constructors `Node` and `Leaf`. Constructor `Leaf` takes just one argument (an integer value for the leaf) and returns a tree, whereas the `Node` constructor takes a tuple with two trees as input and constructs a new tree node.

For instance, the expression

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
designed to be simple with few language constructs, at the right level
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

is order-dependent; any change in pattern order changes which match-arm is executed. To express this in an order-independent manner we `&` every pattern with the inverse (`!`) of the union (`|`) of the previous patterns. If we pretend for a moment that OCaml supports `&` and `!` in patterns they could then be written as:

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
let t0 = tensorCreateDense [] (lam. 'a') in
utest tensorRank t0 with 0 in
utest tensorShape t0 with [] in
```

We can access and mutate elements in a tensor using
```
utest tensorSetExn t0 [] 'b' with () in
utest tensorGetExn t0 [] with 'b' in
()
```

The file [tensor.mc](stdlib/tensor.mc) contains a wide variety of useful tensor
functions. We can import it into a program using the `include`
keyword (more on this [later](#MLang)). We can construct a rank 1
tensor (i.e. vector) as
```
include "tensor.mc"
mexpr
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
tensorSetExn t2 [0, 0] 2;
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
tensorMapInplace (lam. 0) r2;
utest tensorToSeqExn t1 with [2, 2, 3, 0, 0, 0, 7, 8, 9] in
```
where we use `tensorMapInplace` from `tensor.mc`.

We can get a subset of the rows of t2 by restricting its 0th dimension.
```
let s1 = tensorSubExn t2 1 2 in
utest tensorShape s1 with [2, 3] in
utest tensorToSeqExn (tensorReshapeExn s1 [6]) with [0, 0, 0, 7, 8, 9] in
()
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
modref r 4;
utest deref r with 4 in ()
```

Note that the return value of `modref` is an MExpr unit value.

It is possible have aliases for the same memory cell by binding several
variables to the same reference. As an example, in the program

```
let r1 = ref "A" in
let r2 = r1 in
modref r2 "B";
utest deref r1 with "B" in ()
```

the change made to the referenced value via the variable `r2` is visible when
dereferencing the reference via the variable `r1`.

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
Python intrinsics, which allow calling Python code from MCore, are offered as an optional feature for the `boot` bootstrap interpreter.
To build the project with Python integration you need to have [Python 3](https://www.python.org) installed on your system.
You will also need to install any Python libraries you want to use (for example using pip).

In addition, you need the [pyml](https://github.com/thierry-martinez/pyml) OCaml Python bindings, available via `opam`:

```
opam install pyml
```

`boot` will automatically be compiled with Python support when the `pyml` package is installed.

NOTE: Currently, there seems to be a problem with the current OPAM bindings with the multicore switch. If the above command fails, try to run the following and then install `pyml` again:

```
opam pin stdcompat 15
```

To run the Python-specific test suite:

```
make test-boot-py
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
| ()              | None        |
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
| None        | ()              |
| Dict        | Record          |
| Tuple       | Tuple (Record)  |
| other       | N/A             |

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
      { 
        expr = "Float.exp", 
        ty = tyarrow_ tyfloat_ tyfloat_ , 
        libraries = [], 
        cLibraries = [] 
      }
    ])
  ]
```

This map associates the `externalExp` external to a list of expressions in the
target language, which here only has one element, namely the function
`Float.exp` from OCaml's standard library. The field `ty` encode the OCaml type
of this value (see [stdlib/ocaml/ast.mc](stdlib/ocaml/ast.mc)), which is needed
to convert values between miking and OCaml. In the case where you have multiple
implementations, the compiler will try to pick the implementation which gives
the least amount of overhead when converting to and from OCaml values. The
`libraries` field list OCaml libraries that are needed to call this function,
and `cLibraries` lists c libraries that are needed during linking. In this case
none are needed since it is part of the standard library. If let's say we wanted
to use `Float.exp` from a library `foo`, then we should instead have the field
`libraries = ["foo"]`. Finally, we need to add `mathExtMap` to
`globalExternalImplsMap` in
[stdlib/ocaml/external-includes.mc](stdlib/ocaml/external-includes.mc).

### Conversion between values
Conversion between Miking values and OCaml values is defined in
[stdlib/ocaml/external.mc](stdlib/ocaml/external.mc). Since externals are in an
early stage of development these conversions are not complete and subject to
change. 

The following Basic types are converted without any computational overhead:

| **Miking type** | **OCaml type** |
|:----------------|:---------------|
| `Int`           | `int`          |
| `Float`         | `float`        |
| `Bool`          | `bool`         |

The overhead of converting sequences to OCaml data-structures is proportional to
the length of the sequence times the conversion cost for the type of the
elements. Strings in Miking is a special case of sequences.

| **Miking type**      | **OCaml type** | **Comment**                                                                                 |
|:---------------------|:---------------|:--------------------------------------------------------------------------------------------|
| `[A]`                | `'a list`      |                                                                                             |
| `[A]`                | `'a array`     | A copy is made, mutating the OCaml array does not mutate the sequence.                      |
| `[Char]` or `String` | `string`       | The Miking string is converted to, and the OCaml string is assumed to be, encoded in UTF-8. |
    
Tensors are passed by reference to OCaml, i.e. mutating the corresponding
data-structure in OCaml will mutate the tensor. As a temporary solution the
conversion depends on the underlying implementation of the tensor, which is
controlled by the tensor create functions `tensorCreateDense`,
`tensorCreateCArrayInt`, and `tensorCreateCArrayFloat`. The main purpose of the
latter two is to allow data-sharing with C libraries via OCaml bindings.

| **Miking type** | **OCaml type**                                   | **Comment**                                                         |
|:----------------|:-------------------------------------------------|:--------------------------------------------------------------------|
| `Tensor[Int]`   | `Bigarray.((int, int_elt, c_layout) genarray.t)` | Must use `tensorCreateCArrayInt`, otherwise a runtime error occurs. |
| `Tensor[Float]` | `Bigarray.((float, float64_elt, c_layout) genarray.t)` | Must use `tensorCreateCArrayFloat`, otherwise a runtime error occurs. |
| `Tensor[Int]` of rank 1   | `Bigarray.((int, int_elt, c_layout) Array1.t)` | Must use `tensorCreateCArrayInt`, otherwise a runtime error occurs. |
| `Tensor[Float]` of rank 1 | `Bigarray.((float, float64_elt, c_layout) Array1.t)` | Must use `tensorCreateCArrayFloat`, otherwise a runtime error occurs. |

Tuples are converted without overhead if the conversion of their elements are
without overhead. The same is true for arrow types. The fields in Miking records
are un-ordered while they are ordered in OCaml so there is some overhead
involved when converting records as each field of the Miking records needs to be
projected to form an new OCaml records, and vice versa. The fields of the Miking
record are associated with the fields of the OCaml record by an explicit mapping
defined in the `*.ext-ocaml.mc` file.

If the Miking type is abstract, i.e. we define it as 
```
type MyType
```
then no conversion is performed to and from this type.

Please consult [stdlib/ext/ext-test.mc](stdlib/ext/ext-test.mc) and
[stdlib/ext/ext-test.ext-ocaml.mc](stdlib/ext/ext-test.ext-ocaml.mc), for more
examples.

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


### Ipopt
Another example use of externals is an interface to the constrained Non-Linear
Program solver [Ipopt](https://coin-or.github.io/Ipopt/). This interface is
defined in [stdlib/ipopt/ipopt.mc](stdlib/ipopt/ipopt.mc) and
[stdlib/ipopt/ipopt.ext-ocaml.mc](stdlib/ipopt/ipopt.ext-ocaml.mc). This library
depends on both the OCaml library [ipoptml](https://github.com/br4sco/ipoptml)
and the ipopt c library.

To use this library you need to do the following:

Install the ipopt c library, which you can do on ubuntu 20.04 with
```
sudo apt-get install coinor-libipopt-dev
```

Install dependencies for [ipoptml](https://github.com/br4sco/ipoptml),
```
opam install ctypes ctypes-foreign
```

Clone the [ipoptml](https://github.com/br4sco/ipoptml) repo and in its root run
```
dune build
dune install
```

You can then test the solver in Miking with

```
make test-ipopt
```

### External Dependent Utests Pruning
As part of the parsing (see `prune_external_utests` in `parserutils.ml` for
details) utests that depend on externals are marked and removed. This done in
the following steps:
1. Dead code removal is performed to remove dead code, including any dead code
   inside utests that might reference externals. This is done to reduce the
   number of false positivities.
2. Utests that references externals are marked and removed.
3. Dead code removal is run again to remove any dead code that result from the
   removal of utests in step 2.

Additionally, if `boot` or `mi` is run without the `--test` flag, all utests are
removed prior to dead code removal as all utests can then be considered dead
code. This both allows the dead code removal to remove more dead code and
simplifies the pruning of utests implementation. If any utest pruning is
performed, a warning summarizing pruned utests is printed to _stdout_.

The pruning of utests can be disabled with the `--disable-prune-utests` flag and
debugged with `--debug-prune-utests` (only in boot).

Moreover, pruning of utests can be disabled for a selection of externals, which
allows for a more granular approach to the testing of external dependent code
(see below).

#### Selective pruning
During compilation, the available OCaml packages on the
current system is queried and externals depending on these packages are excluded
from utests pruning. In other words, utests that depend on externals that can be
compiled on the system are kept, while all others are removed. The listing of
OCaml packages is based around `dune installed-libraries` (see
`externalListOcamlPackages` and `externalGetSupportedExternalImpls` in
`external-includes.mc` so this functionality should not require any additional
dependencies. For boot and the interpreter, _all_ external dependent utests are
removed as these currently do not support externals at all.

#### Test organization
`make test-all` runs all tests, disabling utest pruning for compiled files
(i.e. if dependencies are not met, you get an error). The recepie `make
test-all-prune-utests` runs all tests but prunes non-supported utests which is
handy if your system only meet the dependencies of a subset of the
externals. Interpreted files are always pruned of external dependent
utests. Please consult the makefiles for more details.

#### Authoring new external libraries
To maintain the flexibility of the test organization, future external libraries
must ensure that externals, or external dependent identifiers are only fully
applied inside utests. To verify that this is the case you can just run `boot
eval --test <file.mc>` and verify that you get a non-zero exit code on the
library that you are currently working on.

### Parallel Programming
Miking offers a set of externals for shared-memory parallelism using
atomic operations and threads running on multiple cores.

The parallel programming primitives consist of atomic references and functions
for creating and synchronizing threads. In addition to the examples below, more
documentation can be found in the standard library at
[stdlib/multicore](stdlib/multicore/).

To use the parallel programming externals, ensure that you are on the
`4.12.0+domains`
[switch](https://github.com/ocaml-multicore/ocaml-multicore/tree/4.12+domains).

#### Atomic References

Atomic references are similar to ordinary references, except that operations
performed on them are *atomic*, which means that no other execution thread can
interfere with the result. In other words, they are safe to use in
multi-threaded execution. Atomic references are provided in
[multicore/atomic.mc](stdlib/multicore/atomic.mc).

`atomicMake` creates a new atomic reference and gives it an initial value. The
value of the atomic reference can be read by `atomicGet`:

```
include "multicore/atomic.mc"
mexpr
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

Functions for handling threads are provided in
[multicore/threads.mc](stdlib/multicore/threads.mc).
The following example program spawns 10 threads that compete for printing their
IDs:

```
include "string.mc"
include "multicore/thread.mc"
mexpr
let place = atomicMake 1 in
let threads = create 10 (lam. threadSpawn (lam.
  print (join
    [int2string (atomicFetchAndAdd place 1)
    , ": thread ID "
    , int2string (threadSelf ())
    , "\n"
    ]))
) in
map threadJoin threads
```

where `threadSpawn` takes a function of type `() -> a` as argument
and `threadSelf` returns the ID of the current thread. Note that
`threadJoin` must be called once for each call to `threadSpawn`. The
output of the above program might be:

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

#### Synchronization

Externals for thread synchronization in the form of mutual exclusion locks and
condition variables are defined in
[multicore/mutex.mc](stdlib/multicore/mutex.mc) and
[multicore/cond.mc](stdlib/multicore/cond.mc), respectively.

### Probability distributions
Externals for probability distributions are defined in `stdlib/ext/dist-ext.mc`. To use these, you must install the `opam` package `owl` (i.e., `opam install owl`)

## Profiling

Profiling of an MExpr program can be enabled using the `--debug-profile` flag
when compiling or evaluating a program. While this flag also exists in the boot
interpreter, it produces a subset of profiling information than the profiling
approach used in `mi` (which is what is detailed below).

### Profiling output

The profiling results are stored in a file `mexpr.prof` in the current working
directory. If such a file already exists, it will be overwritten. This file
is created when:
* The execution of a compiled program, which had been compiled with the
  `--debug-profile` flag enabled, terminates.
* The interpreter of a program terminates, and the `--debug-profile` flag was
  enabled.

Note that no profiling information is generated during the compilation step,
because the profiling code is instrumented into the produced binary.

#### Output format

The profiling output contains one line per top-level function in the program,
excluding those that are never used during an execution of the program. The
order of the lines is based on the order in which the functions have been
defined in the program. Functions defined in included files will also be listed
in the profiling output, given that they are used.

Each line of output consists of five space-separated columns:
1. A string, denoting the name of the file and the position within the file,
   encoded as `[<start row>:<start col>-<end row>:<end col>]`, where the function
   is defined.
2. A string, denoting the name of the function.
3. An integer, denoting the number of calls made to the function. The counter
   includes self-recursive calls.
4. A floating-point number, denoting the exclusive time spent in the function.
   This is the time spent in a call, except the time spent in calls to other
   top-level functions (including itself).
5. A floating-point number, denoting the inclusive time spent in the function.
   This is the total time spent in all calls to the function, including that
   spent in calls to other top-level functions. As this includes self-recursive
   calls, this value may be greater than the total runtime.

#### Postprocessing

The output format was chosen to be easily sorted using external tools, such as
the `sort` command in Unix. Below we provide two examples of how the output can
be sorted. These assume that the profiling output is stored in `mexpr.prof` and
that the sorted profiling output should be stored in `sorted.prof`.

To sort the functions by the number of times they were called, with the most
frequently called function at the top:
```
cat mexpr.prof | sort -k3 -r -n > sorted.prof
```

To sort the functions by the exclusive time spent within them, placing the
function with the highest exclusive time at the top:
```
cat mexpr.prof | sort -k4 -r -g > sorted.prof
```

### Notes

This instrumentation is currently only performed on functions defined on the
top-level in a program. The runtime of local functions and intrinsic functions
is instead added to the top-level function in which they are used. In addition,
partially applied functions are not profiled.

Importantly, this profiling works by instrumenting the code with extra calls.
The runtime overhead when enabling this flag is significant, especially when
using the evaluator.

## Acceleration

When compiling using `mi compile`, expression acceleration can be enabled via
the `--accelerate` flag. When enabled, parts of the program is compiled in an
accelerated mode, as controlled by the `accelerate` expression. The main part
of the program is compiled to the default backend (OCaml), while expressions
used in `accelerate` expressions are compiled to an accelerate backend, chosen
automatically by the compiler.

### Accelerate backends

The current compiler has support for two different accelerate backends, both of
which require a GPU to compile the code. The Futhark backend is used when at
least one of the `map`, `map2`, or `reduce` parallel keywords are used within
an accelerated expression. To make use of this backend, `futhark` and its
dependencies must be installed
(see [installation instructions](https://futhark.readthedocs.io/en/stable/installation.html)).
If the `loop` parallel keyword is used in an accelerated expression, the CUDA
backend is used. At least one of these keywords must be used in the accelerated
code, or the compiler will complain as the accelerated code would execute
sequentially.

Both backends currently require an installation of CUDA. In addition, the CUDA
backend requires an Nvidia GPU with support for unified memory (Kepler
architecture or later).

### Usage

When enabling acceleration via `mi compile --accelerate`, the parallel keywords
must be used for parallel execution. Any code used in an `accelerate` is passed
to the automatically chosen accelerate backend. Within such code, certain
parallel keywords must be used to execute on the GPU. The parallel keywords
supported in the Futhark backend are `map`, `map2`, and `reduce`. For the CUDA
backend, this is `loop`. Note that there are limitations on what kinds of
expressions can be accelerated. The compiler will report errors in such cases.

When compiling without enabling acceleration, the `accelerate` expressions in
the program are ignored, and all parallel constructs are executed sequentially.

#### Recommended workflow

The recommended workflow when using acceleration is as follows. First, develop
the program in *debug mode*, using the `--debug-accelerate` flag. This enables
static well-formedness checks plus additional dynamic checks for the
accelerated code, plus provides improved error messages on errors for built-in
functions. This mode produces significantly better error messages than when
compiling without any flags, but has an impact on the runtime performance.

Once the program in debug mode works as expected, the program is compiled in
*accelerate mode*. In this mode, the `--accelerate` flag is set to enable
acceleration. The accelerated binary produced when compiling in accelerate mode
does not fail given that the debug binary did not fail.

Note that the `--debug-accelerate` and `--accelerate` flags are mutually
exclusive. That is, you cannot use both configurations simultaneously.

#### Example

Assume the program below is saved in a file `example.mc`.

```
mexpr
let f = lam x. addi (muli x 2) 1 in
let s = [1,2,3] in
accelerate (map f s) -- result = [3,5,7]
```

If we compile the program as `mi compile example.mc`, acceleration is disabled,
so the `map` is executed sequentially. However, if the program is compiled
using `mi compile --accelerate example.mc`, the `map` function `f` is applied
to the elements of `s` in parallel, on the GPU. In this case, as we make use of
`map`, it will execute using the Futhark backend.

See the [accelerate examples](test/examples/accelerate) directory for more
examples.

### Sequence sizes

A significant difference between MExpr and Futhark is that the latter includes
the size of a sequence as part of its type. This means that, for example, when
a function returns a two-dimensional sequence, the inner sequences must all
have the same size (otherwise they would have different types). As this is not
required by MExpr, there are situations where one may need to provide
additional information in MExpr to help the Futhark compiler.

Such information is provided through `utest` expressions of specific shapes.
The idea is that, when the program is compiled in debug mode, the `utest`
expressions are checked at runtime. If such a `utest` fails at runtime when
compiled in debug mode, it would also fail in the accelerated code, but likely
with a less understandable error message.

In the future, the accelerate compiler will statically check that the necessary
size constraints have been added. For now, failing to provide sufficient
information results in a Futhark compilation error.

#### Size coercions

Consider the following example

```
mexpr
let g : [Int] -> [Int] = lam s. snoc s 5 in
let f : [[Int]] -> [[Int]] = lam s. map g s in
let s : [[Int]] = [[1,2],[3,4]] in
let s : [[Int]] = accelerate (f s) in
s
```

In the function `g`, the size of the array is increased because `snoc` appends
an integer element to the end of the given sequence. In this case, the size of
the output sequence is not the same as the size of the input sequence. Because
of this, the Futhark compiler cannot show that all inner sequences produced in
the `map` of the `f` function will have the same size.

We can show this by adding a `utest` of the shape `utest length s with n in e`
within the inner function. Here `s` is an expression referring to a sequence
and `n` is a variable from an outer scope (or a parameter), such that the
compiler knows it is the same for every inner sequence. We rewrite `f` as

```
let f : [[Int]] -> [[Int]] = lam s.
  -- 'n' is defined outside the map function so that the compiler knows this
  -- size will be the same for every inner sequence.
  let n = addi (length s) 1 in
  map
    (lam inner : [Int].
      let inner : [Int] = g inner in
      utest length inner with n in
      inner)
    s
in
```

#### Size equality

Consider the following implementation of the transpose operation on a square
matrix:

```
let transposeSq : [[Int]] -> [[Int]] = lam m.
  let n = length m in
  create n (lam i : Int.
    let inner : [Int] = create n (lam j : Int. get (get m j) i) in
    inner)
in
...
```

The implementation accepts a matrix of any form, even though this would only
work for a square matrix. By inserting a `utest` of the form
`utest length m with length (head m) in e` (we assume inner dimensions are
non-empty), we can express an equality constraint between the first two
dimensions of the matrix `m`, which may be needed when this function is used in
other places.

### Limitations

There are limitations on what kinds of expressions can be accelerated. The
exact limitations depend on which accelerate backend is used. They apply to
the accelerated expressions and any code these make use of. Many limitations
are checked statically when compiling with `--accelerate`. When using
`--debug-accelerate`, a few limitations are also checked dynamically.

In addition, we assume that the parallel operations performed in a `reduce` or
`loop` yield the same result regardless of execution order. If this requirement
is not met, the results may vary between executions.

## Auto Tuning

An MExpr program can contain decision variables, or so called holes, whose
values are to be decided by an autotuner. A hole is introduced into a program
using the keyword `hole`. The `hole` takes as argument the type of the hole
(either `Boolean` or `IntRange`) and its default value. Additionally, an
`IntRange` hole expects a minimum and maximum value.

For example, the following defines a function `sort` that chooses sorting
algorithm based on input data length.

```
let sort = lam seq.
  let threshold = hole (IntRange {default = 10, min = 0, max = 10000}) in
  if leqi (length seq) threshold then insertionSort seq
  else mergeSort seq
in
```

We can invoke the autotuner using the `mi tune` subcommand:

```
mi tune sort.mc
```

The autotuner uses offline profiling in order to assign the holes values such
that the execution time of the program is minimized. Available command-line
options (for setting search strategy, stopping condition, etc.) are listed in
`stdlib/tuning/tune-options.mc`.

The result of `mi tune` is a tune file, which by default is written to
`sort.tune` (if your program is called `sort.mc`). To compile the program using
the tuned values, invoke the main compiler with the `--tuned` option:

```
mi compile --tuned sort.mc
```

Passing the `--tuned` flag to `mi tune` makes the auto tuner restart the tuning
using the values in the tune file as start values:

```
mi compile --tuned sort.mc
```

To tune and compile the program in one go, provide the `--compile`
flag to `mi tune`:

```
mi tune --compile sort.mc
```

Note that `mi compile sort.mc` compiles the program using the default values of
the holes.

### Context-Dependent Holes

A `hole` takes an additional (optional) parameter `depth`, which represents the
length of the most recent function call history that should influence the choice
of the value of the hole. By default (if not provided), then `depth` is 0, which
means that the hole is assigned one value globally by the autotuner. If `depth`
is larger than 0, then the hole is potentially assigned a different values for
each possible context.

For instance, the following defines a function `hcreate` that chooses between
two sequence representations:

```
let hcreate = lam n. lam f.
  let rope = hole (Boolean {default = true, depth = 1}) in
  (if rope then createRope else createList) n f
in
```

The hole `rope` has `depth` one, which means that its value might be different
for two different calls to `hcreate`.

## Contributing

1. Before making a pull request please make sure that all tests pass. Run
appropriate tests as described above.

2. Make sure you follow the conventions declared in the
[wiki](https://github.com/miking-lang/miking/wiki/Conventions).

3. We use [ocamlformat](https://github.com/ocaml-ppx/ocamlformat) to
automatically format ocaml source code.

###  Setup and use `ocamlformat`

We are currently using this package at version `0.20.1`. To pin and/or install
the package at this version using `opam` do
```
opam pin ocamlformat 0.20.1
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

Copyright 2017-2021 David Broman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
