# Introduction

This file gives a basic runthrough of the in-progress design of a DSL
for syntax and AST specification.

## Basics

```
-- Line comments

/-
Multiline comments
-/
```

We declare new types in the AST and non-terminals in
the grammar with `type`.

```
type Expr
```

A constructor in the AST and production in the grammar is introduced
with `prod`.

```
prod TmInt: Expr = value:Int
```

Each constructor gets its own language fragment in the generated code,
thus the above yields the following fragment:

```
lang TmInt
  syn Expr =
  | TmInt { value : Int }
```

The syntax of a single production can contain regex style repetition
operators:

```
-- Repeated field names are collected into a sequence in the
-- order they appear in the source.
prod TmTuple: Expr = "(" fields:Expr ("," fields:Expr)+ ")"
-- Zero-or-more is expressed with `?` and produce an Option
prod TmLet: Expr = "let" ident:LIdent (":" tyIdent:Type)? "=" value:Expr "in" body:Expr
```
We can also give the constructor nested records:

```
prod TmMatch: Expr = "match" target:Expr "with" arms:{"|" pat:Pat "->" body:Expr}+
```

```
lang TmMatch
  syn Expr =
  | TmMatch { target : Expr, arms : [{pat : Pat, body : Expr}]}
end
```

Explicit grouping (i.e. parentheses) should not be specified as a
production but rather explicitly as grouping:

```
grouping "(" Expr ")"
```

It should have the form `grouping` `<token>` `<type>` `<token>`.

### Tokens

Tokens can be either a literal (e.g. `"let"`) or a named token
(e.g. `LIdent`). In the current system there is a number of builtin
token types, currently specified in `lexer.mc`.

## Operators

Operators can be written either explicitly:
```
prod TmAdd: Expr = left:Expr "+" right:Expr
```

...or with syntactic sugar:
```
infix TmMul: Expr = "*"

-- Similarly for prefix and postfix
prefix TmNot: Expr = "!"
postfix TmFieldAccess: Expr = "." field:LIdent
```

Each production will be one of these things:
- Simple/atomic if it has no direct recursion on either edge
- Prefix if it only has direct recursion on the right edge
- Postfix if it only has direct recursion on the left edge
- Infix if it has direct recursion on both edges

I suspect that productions that sometimes have direct recursion on the
edge and sometimes not are a bad idea. Please let me know if such
cases come up, so we can see if that is correct or not.

Infix productions can specify their associativity:

```
prod left TmSub: Expr = left:Expr "-" right:Expr
infix left TmDiv: Expr = "/"
```

## Precedence

Precedence is primarily specified with a precedence table:

```
precedence {
  TmFieldAccess;
  TmNot;
  TmMul TmDiv;
  TmAdd TmSub;
}
```
Note that only non-simple productions can appear in a precedence list,
i.e., operators; those that are prefix, postfix, or infix.

Operators appearing earlier in the list (i.e. higher) have higher
precedence than operators appearing later. Operators on the same
level have the same precedence.

### Same Precedence

To see what happens when two operators have the same precedence we
first need to look at their associativity. Note that prefix operators
associate to the right by definition, and postfix operators associate
left.

- If the operators have the same associativity then grouping will
  follow that associativity. For example, given left-associative
  addition and subtraction on the same precedence, `a - b + c` is
  `(a - b) + c`.
- If the operators do not have the same associativity grouping becomes
  ambiguous.

### Exceptions

It is also possible to write a precedence table that is not total by
specifying which relations should *not* be defined through this table:

```
precedence {
  mul div;
  add sub;
  equal notEqual less greater;
} except {
  equal notEqual less greater;
}
```

Each line in the `except` block makes precedence undefined between
each possible pair of operators on the line. In this case, e.g.,
`equal` and `notEqual` do not have defined relative precedence, nor
does `notEqual` and `greater`.

## Broken Productions

Productions that use the regex repetition operators can be broken
apart into multiple operators for the parsing stage, then
automatically reassembled when the AST is constructed. This makes it
possible to perform disambiguation through precedence and
associativity, and also to produce ambiguity error messages.

Ideally this should happen entirely automatically with no need for
additional annotations, thus this section should not be required
reading in most cases.

However, it will affect error messages for bad grammars. I believe it
should not introduce new cases where grammars are bad, rather make
some grammars accepted that otherwise wouldn't be and change the
errors for others, but I'm not sure yet.

The specifics of this are not yet known to me, but I suspect the
following will be true:

A repetition will be broken out to a new operator if it can end up
adjacent to a direct recursion. For example:

```
-- Note that `?` is a repetition, just a very simple one
prod if: Expr = "if" cond:Expr "then" then:Expr ("else" else:Expr)?
```

Note that a `*` or `+` repetition that has direct recursion at the
edge will trivially be adjacent to direct recursion:


```
prod match: Expr = "match" target:Expr "with" arms:{"|" p:Pat "->" body:Expr}+
```
