
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

* **MLang** which is a language for composing language fragments. MLang is formally translated into an MExpr.



## MExpr

One design objective of MExpr is to make the concrete syntax very close to the abstract syntax of the language. That is, no syntactic sugar is introduced to the concrete MCore syntax. The MCore language is not intended to be a general purpose programming language, but a core language to which other languages translate into.



### Terms


### Constants






## MLang







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
