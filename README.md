
# Miking

Miking (Meta vIKING) is a meta language system for creating embedded
domain-specific and general-purpose languages.

Miking is not a programming language, but rather a language system for
creating languages and generating efficient compilers.


## MCore
MCore (Miking Core) is the core language of the Miking system. It is based on a typed Lambda Calculus. Unique features of the MCore language are:

* The **Dive** operator that enables runtime partial evaluation and meta programming.
* The **Compose** operator that makes it possible to compose new languages from existing language fragments.
* **Unified Collection Types (UC Types)**, a unified approach to handle standard collections, such as sequences, lists, maps, multisets, sets, and more.

The rest of this document gives a brief overview of the MCore language.

### Syntax
One of the design objectives of MCore is to make the concrete syntax very close to the abstract syntax of the language. That is, no syntactic sugar is introduced to the concrete MCore syntax. The MCore language is not intended to be a general purpose programming language, but a core language to which other languages translate into.

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


## Pure MCore

MCore is an extension to Pure MCore that includes various syntactic sugar extensions. The
main extensions are:

* Inference of self variables.

* Syntactic sugar for `let in` and `if` expressions.

* An implicit definition of the default module with self variable `root`.

### Inference of Self Variables

The following program in MCore

```
let m1 = {
  let foo = 7
}
let x = m1.foo  // x contains value 7
```
is a syntactic simplification of Pure MCore, where the self variables have been derived. In the following version, the two self variables `s` and `root` are explicit.

```
let m1 = self s {
  let foo = 7
  let x = s.foo + 1   // x evaluates to 8
}
let y = root.m1.foo   // y evaluates to 7
```

In the above code, the top level module was implicit, using a default self variable called `root`. In the following complete Pure MCore code, this module is also explicit:

```
self root {
  let m1 = self s {
    let foo = 7
    let x = s.foo + 1   // x evaluates to 8
  }
  let y = root.m1.foo   // y evaluates to 7
}
```

## Other

The following things need to be described in the text:

* First-class modules.

* The use of public labels in modules.

* Composition of modules and functions.

* Why integers, floating-point numbers, and booleans are data types.

* Expansion of `let in` expressions.

* Expansion of `if` expressions into `match` expressions.

Example of a program with polymorphic data types

```
lang mcore

// Define a data type
tcon Tree(*)

// Define two data constructors
dcon all A. Node(Tree(A),Tree(A)) => Tree(A)
dcon all A. Leaf(A) => Tree(A)

// Create a term of data type Tree
let t1 = Node(Node(Leaf(1),Leaf(2)),Leaf(3))

let countLeafs = lam t:Tree.
  match t with
    case Node(n1,n2) => addi (countLeafs n1) (countLeafs n2)
  | case Leaf(_) => 1
```


## MIT License
Miking is licensed under the MIT license.

Copyright 2017-2019 David Broman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
