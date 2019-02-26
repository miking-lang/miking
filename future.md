
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





## MIT License
Miking is licensed under the MIT license.

Copyright 2017-2019 David Broman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
