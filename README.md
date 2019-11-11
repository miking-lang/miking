
# Miking

Miking (Meta vIKING) is a meta language system for creating embedded
domain-specific and general-purpose languages.

Miking is not a programming language, but rather a language system for
creating languages and generating efficient compilers.

## Getting started

Before you test the Miking system, you need to install
[OCaml](https://ocaml.org/), the
[OPAM](https://opam.ocaml.org/) package manager, and the `dune`
package. To compile and run the test suite, execute

```
>> make test
```
on the command line.

A bootstrap interpreter is available under `build/boot` after compiling the project. To run a hello world program, create a file `hello.mc` with the following code

```
main
  print("Hello world")
```

and then run it using command

```
>> build/boot hello.mc
```





## MCore

MCore (Miking Core) is the core language of the Miking system. It is
based on a typed Lambda Calculus (Note: the type system is under
development, and the current implementation is untyped).

MCore consists of two parts:

* **MExpr** is an MCore expression. A Miking language is always translated into an MExpr, before it is further evaluated or compiled into machine code.

* **MLang** which is a language for defining and composing language fragments. MLang is formally translated into an MExpr.



## MExpr

One design objective of MExpr is to make the concrete syntax very close to the abstract syntax of the language. That is, no syntactic sugar is introduced to the concrete MCore syntax. The MCore language is not intended to be a general purpose programming language, but a core language to which other languages translate into.



### Terms


### Constants






## MLang

MLang is a superset of MExpr, and is used to define and compose
reusable language fragments. It also supports top-level
definitions and simple file inclusion. The definitions can be
translated into pure MExpr definitions, and can be run as any
other MExpr programs.

### Top-Level Definitions and Includes

Values, types and data constructors can be defined top-level,
before the `main` keyword of an MCore program. The syntax is
identical to that of the corresponding MExpr definitions, without
the trailing `in`:

```
let id = lam x. x
type T
con Foo : Int -> T

main

utest id (Foo 42) with Foo 42 in
()
```

The translation into MExpr is straightforward: the definitions are
simply moved into the beginning of the `main` program. The
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
language fragments can be defined before the `main` keyword in an
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
main
use Arith in
utest eval (Add (Num 2, Num 3)) with Num 5 in
()
```

A `use` is translated into a series of MExpr definitions which
match the syntax and semantics of the specified language fragment.

An important feature of language fragments is that they can be
composed to form new language fragments. As an example, we might
want to extend our arithmetics language with booleans and if
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

main

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
be used expressions other than integers. In order to cater to such
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

main

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


## Other

The following section contains notes about concepts that are not yet part of the Miking system, but might be introduced at a later stage.

### Unfied Collection Types (UC Types)

UC Types unify the concepts typically implemented in abstract data types such as lists, maps, and sets. Instead of being different data types, there is one unified type with two different properties: **Order** and **Uniqueness**.

**Property 1 (Order):**

* Unordered (U)
* Ordered (O)
* Sorted (S)

**Property 2 (Uniqueness):**

* Unique (Q)
* Multivalued (M)

Each combination of the two properties form a *specific* collection type:

1. Properties *Unordered* and *Unique* forms a **Set**
2. Properties *Unordered* and *Multivalued* forms a **Multi Set**
3. Properties *Ordered* and *Unique* forms a **Unique Sequence**
4. Properties *Ordered* and *Multivalued* forms a **Sequence**
5. Properties *Sorted* and *Unique* forms a **Sorted Set**
6. Properties *Sorted* and *Multivalued* forms a **Sorted Multi Set**

Each of these collection types can then be used as other standard data type. For instance, a sequence can be used as a list, an immutable array, a queue, or a stack. Functional maps can be defined using sets, where the values are maplets (only the key of a maplet is compared). Priority queues can be created using maplets and sorted sets.

UC types have many different intrinsic functions (built-in functions), where some of them are only valid for some of the 6 specific collection types. Moreover, there are some operations defined on the *composition* of collection types. For instance, a matrix can be defined as a sequence of sequences, where matrix multiplication is defined on such a type.


## MIT License
Miking is licensed under the MIT license.

Copyright 2017-2019 David Broman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
