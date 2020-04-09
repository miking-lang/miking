
# Miking

Miking (Meta vIKING) is a meta language system for creating embedded domain-specific and general-purpose languages. Miking is not a programming language, but rather a language system for
creating languages and generating efficient compilers.

## Getting started

Before you test the Miking system, you need to install
[OCaml](https://ocaml.org/), the
[OPAM](https://opam.ocaml.org/) package manager, 
The packages `dune` and `batteries`.

After installing `opam`, these packages can be installed as:

```
>> opam install dune batteries
```

To compile and run the test suite, execute

```
>> make test
```

A bootstrap interpreter is available under `build/boot` after compiling the project. To run a hello world program, create a file `hello.mc` with the following code

```
mexpr
  print("Hello, world!\n")
```

and then run it using command

```
>> build/boot hello.mc
```

To help Miking find its standard library, you should define the
environment variable `MCORE_STDLIB` to be the path to `stdlib`,
for example by running the following:

    cd stdlib; export MCORE_STDLIB=`pwd`; cd ..;

To install the boot interpreter along with the standard library for the current
user, issue:

```
>>> make install
```

### Sundials integration
To build the project with sundials integration you need to install the
[Sundials](https://computing.llnl.gov/projects/sundials) libraries on your
system.

This involves installing the C library. On `ubuntu 18.04` you can issue:

```
>> sudo apt-get install libsundials-dev
```

On `macOS`, using Homebrew, you can install Sundials using command:

```
>> brew install sundials
```


Then install the ocaml bindings
[SundialsML](https://inria-parkas.github.io/sundialsml/) via `opam`

```
>> opam install sundialsml
```

To compile and run the test suite with sundials support:

```
>> make externals-test
```

To install for the current user:

```
>>> make externals-install
```

## Editor Support

It is possible to write Miking code in any editor and compile it
via the command line. There is, however, an Emacs mode in
`emacs/mcore-mode.el` that defines syntax highlighting and
compilation support. To use it, add the following to your
`init.el` file:

```
;; MCore mode
(add-to-list 'load-path "/path/to/miking/emacs/")
(require 'mcore-mode)
```

(or run `M-x eval-buffer` in the file defining the mode)


## MCore

MCore (Miking Core) is the core language of the Miking system. It is
based on a typed Lambda Calculus (Note: the type system is under
development, and the current implementation is untyped).

MCore consists of two parts:

* **MExpr** is an MCore expression. A Miking language is always translated into an MExpr, before it is further evaluated or compiled into machine code.

* **MLang** which is a language for defining and composing language fragments. MLang is formally translated into an MExpr.



## MExpr

One design objective of MExpr is to make the concrete syntax very close to the abstract syntax of the language. That is, no syntactic sugar is introduced to the concrete MCore syntax. The MExpr language is not intended to be a general purpose programming language, but a core language to which other languages translate into.

Nevertheless, to understand the Miking system, it is a good idea to learn to write basic programs directly as MCore expressions.

An MCore file `.mc` is in the end always translated into an MCore expression. If an MCore file contains `mexpr 5`, it means that the final expression of the program is value `5`. That is, `mexpr` states the start of the program and is followed by the actual MExpr of the program. If the keyword `mexpr` is left out of the file, a default mexpr unit value `()` is the resulting value.

### Prelude

MCore contains a number of built-in values and predefined functions and constants. These are defined in the [prelude](doc/prelude.md) documentation. For instance, the program

```
mexpr
print "Hello"
```

uses the built-in function `print` which has the type `String -> Unit`, i.e., it prints a string and returns the unit type. In the rest of this section, we will leave out the `mexpr` keyword, and just write the MExpr itself.



### Let Expressions

Expressions can be given names using `let` expressions. For instance

```
let x = addi 1 2 in
x
```

introduces a new name `x`. The build in function `addi` performs an addition between two integers. Note that MCore has a call-by-value semantics, which means that expressions are evaluated into a value before they are applied to a function or substituted using a `let` expression. Hence, the expression `addi 1 2` is evaluated before it is substituted for `x` in the rest of the expression.


### Unit Test Expressions

When writing MCore programs, it is typically done by writing explicit unit tests as part of the code. For instance

```
utest addi 1 2 with 3 in
()
```
checkes that the addition of `1` and `2` is in fact `3`. Typically when you develop MCore programs, you do not use the `print` function. Instead, you write unit tests directly, and then leave the units tests as is directly after your function. By doing so, you test your code, write regression tests, and document the informal semantics of your program directly. We strongly encourage you to develop your MCore programs this way.

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
let double : Int -> Int = lam x:Int. muli x 2 in
```

A function with several parameters are expressed using currying, using nested lambda expressions. For instance, expression

```
let foo = lam x. lam y. addi x y in
utest foo 2 3 with 5 in
()
```
creates a function `foo` that takes two arguments.

### `if` Expressions

Conditional expressions can be expressed using `if` expressions. The program

```
let x = 5 in
let answer = if (lti x 10) then "yes" else "no" in
utest answer with "yes" in
()
```

checks if `x` is less than 10 (using the `lti` function with signature `Int -> Int -> Bool`). If it is true, the string `"yes"` is returned, else string `"no"` is returned.

### Recursion

Using only lambdas and `let` expressions are not enough to express recursive functions. Instead, a fixed-point term is used, called `fix`.

Consider the factorial function

```
let fact = fix (lam fact. lam n.
  if eqi n 0
    then 1
    else muli n (fact (subi n 1))
) in

utest fact 4 with 24 in
()

```

We define a recursive function `fact` by using the fixed-point combinator `fix`. This means that when the inner `fact` will "copy itself", thus resulting in a recursive call.

See the [prelude](doc/prelude.md) documentation for details on `eqi`, `muli`, and `subi`.

### Tuples

Product types are expressed using tuples. An n-tuple is defined using syntax `(e_1, ..., e_n)` where `e_1` to `e_n` are MCore expressions. Extracting a value from a tuple (projection) is performed using an expression `e.n` where `e` is the expression that is evaluated into a tuple, and `n` is an integer number representing the index of an element in the tuple. The first intex in a tuple is `0`.

For instance, in the MCore expression

```
let t = (addi 1 2, "hi", 80) in
utest t.0 with 3 in
utest t.1 with "hi" in
utest t.2 with 80 in
()
```
we create a 3-tuple `t` and project out its values. Note that the different elements of a tuple can have different types. In this case, tuple `t` has type `(Int, String, Int)`.

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
let count = fix (lam count. lam tree.
	match tree with Node t then
	  let left = t.0 in
	  let right = t.1 in
	  addi (count left) (count right)
	else match tree with Leaf v then v
	else error "Unknown node"
) in
```

The `count` function performs recursion using the fixed-point term `fix`.

The `match` expression inside the count function *deconstructs* data values by matching against a given constructor. For instance, the `match` expression

```
match tree with Node t then expr1 else expr2
```

matches the value after evaluating expression `tree` and checks if its outer most constructor is a `Node` constructor. If that is the case, the identifier `t` in expression `expr1` is bound to the tuple consisting of the node's two sub trees (recall the definition of the constructor `Node`).

As part of the design of MExpr, we try to make it simple. Hence, MExpr does not support pattern variables or nested matches. This should instead be introduced by languages that are later compiled into an MExpr. This is the reason for the pattern where `left` and `right` identifiers are introduced by projecting out the elements from a tuple.

Finally, if we execute the test

```
utest count tree with 9 in ()
```

we can check that the function computes the result as intended.

### Sequences

An MCore sequence is constructed using syntax `[e_1, ..., e_n]`. All elements in an sequence must have the same type. For instance, an expression

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

or the `nth` function picks out the nth element of a sequence

```
utest nth [3,5,8,9] 2 with 8 in ()
```

See the [prelude](doc/prelude.md) document for more information.




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
`include "path/to/prog.mc"` before any top-level definitions in a
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
unavailable. When `MCORE_STDLIB` is defined, the file "prelude.mc"
is automatically included.


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
  | Add t ->
    let e1 = t.0 in
    let e2 = t.1 in
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
expr
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
lang Bool
  syn Expr =
  | True
  | False
  | If (Expr, Expr, Expr)

  sem eval =
  | True -> True
  | False -> False
  | If t ->
    let cnd = t.0 in
    let thn = t.1 in
    let els = t.2 in
    let cndVal = eval cnd in
    match cndVal with True
    then eval thn
    else match cndVal with False
    then eval els
    else error "Not a boolean"
end

lang ArithBool = Arith + Bool

mexpr

use ArithBool in
utest eval (Add (If (False, Num 0, Num 5), Num 2)) with Num 7 in
```

The language fragment `ArithBool` is indistinguishable from a
language fragment with all the syntactic and semantic cases of
`Arith` and `Bool` merged. If we wanted, we could have added new
cases to the language composition as well, and refer to the syntax
and semantics of the fragments being composed:

```
lang ArithBool = Arith + Bool
  syn Expr =
  | IsZero Expr

  sem eval =
  | IsZero e ->
    match eval e with Num n then
      if eq n 0 then True else False
    else
      error "Not a number"
end
```

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

### Known Issues/Future Work

* Pattern matching in interpreters is shallow, which sometimes
  requires defining interpreters in multiple "layers" to maintain
  extensibility.
* Interpreters are always defined on pattern matching on a single
  parameter, which also forces the programmer to define several
  interpreters to achieve the same thing.
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






## MIT License
Miking is licensed under the MIT license.

Copyright 2017-2019 David Broman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
