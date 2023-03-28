# Introduction

This file gives a basic runthrough of the in-progress design of a DSL
for syntax and AST specification.

## Running the tool

The tool is currently not sufficiently annotated to be compilable
(it's not yet possible to annotate the final argument of a `sem`
function, I'll fix that once we're a bit further along), thus it can
presently only be interpreted. Assuming we're currently at the root of
the `miking` repository:

```bash
MCORE_LIBS=stdlib=`pwd`/stdlib mi eval stdlib/parser/tool.mc -- test/examples/expr.syn
```

The tool presently only supports a subset of what's described in this
document, and gives either errors or the generated output on standard
out.

## Basic syntax and AST structure

```
-- Line comments

/-
Multiline comments
-/
```

We declare new types in the AST and non-terminals in the grammar with
`type`:

```
type Expr
```

A constructor in the AST and production in the grammar is introduced
with `prod`.

```
prod Int: Expr = value:Integer
```

Each constructor gets its own language fragment in the generated code,
thus the above yields the following fragment:

```
lang IntExprAst
  syn Expr =
  | IntExpr { value : Int, info : Info }

  sem get_Expr_info =
  | IntExpr x -> x.info
end
```

At this point a few things bear mention:
- The `info` field is automatically added and contains the source code
  location of the parsed node. An accessor function is automatically
  generated for this field: `get_Expr_info`.
- By default we append the name of the type to the constructor name,
  i.e., `IntExpr` instead of merely `Int`. If desired this can be
  disabled, see more detailed information on the `type` construct.
- `Integer` on the right-hand side of the production refers to the
  builtin token type `Integer`. These are described in more detail
  later, but here are some commonly used token types:
  - `Integer`, `Float`, `Char`, and `String` for literals.
  - `LIdent` and `UIdent` for lower-case and upper-case identifiers,
    respectively.

Operators can be defined explicitly or with some syntactic short-hand:

```
prod Add: Expr = left:Expr "+" right:Expr
infix Mul: Expr = "*"
```

Note the use of `"+"` and `"*"`; these introduce "keywords" (in this
case operators) that should appear verbatim in the source code.

```
lang AddExprAst
  syn Expr =
  | AddExpr { left : Expr, right : Expr, info : Info }

  /- Some content omitted here -/
end

lang MulExprAst
  syn Expr =
  | MulExpr { left : Expr, right : Expr, info : Info }

  /- Some content omitted here -/
end
```

Note that `AddExpr` and `MulExpr` are largely identical. Similarly,
you can use `prefix` and `postfix` as shorthand for unary operators:

```
prefix Negate: Expr = "-"
-- ...is the same as:
prod Negate: Expr = "-" right:Expr

postfix FieldAccess: Expr = "." label:LIdent
-- ...is the same as:
prod FieldAccess: Expr = left:Expr "." label:LIdent
```

The omitted content in the above fragments define a number of helper
functions. First is `get_Expr_info : Expr -> Info`, as mentioned
earlier, but then there are some additional functions meant to assist
in traversing an AST:

- `smap_Expr_Expr : (Expr -> Expr) -> Expr -> Expr`, for mapping over
  the direct children of the given `Expr`. A version of this function
  is given for every relevant pair of non-terminals used, e.g.,
  `smap_Expr_Type : (Type -> Type) -> Expr -> Expr` also exists
  (assuming `Type` is declared as a non-terminal, i.e., there is a
  `type Type` somewhere). In general, we can read `smap_X_Y` as a
  _shallow mapping_ over every `Y` that is a direct child of the given
  `X`.
- `sfold_Expr_Expr : all acc. (acc -> Expr -> acc) -> acc -> Expr ->
  acc` is the (left-) folding equivalent of `smap_Expr_Expr`.
- `smapAccumL : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Expr
  -> (acc, Expr)` both maps and folds at the same time, and is thus
  more general than `smap` and `sfold`.

These helpers make it easier to write generic code that traverses an
AST. For example, we could count the number of sub-expressions in an
expression with the following function:

```
recursive let countExprs
  : Expr -> Int
  = lam expr.
    sfold_Expr_Expr (lam count. lam e. addi count (countExprs e)) 1 expr
```

This function will work for any expression and does not need any code
that is specific to a particular kind of AST-node. See the Recursion
Cookbook for more on this style of tree traversal.

Returning to the syntax of productions, the right-hand side of a
production can use regex-style `+` (one or more), `*` (zero or more),
`?` (zero or one), and `|` (left or right):

```
-- Repeated field names are collected into a sequence in the
-- order they appear in the source, i.e., left-most first.
prod Tuple: Expr = "(" fields:Expr ("," fields:Expr)+ ")"

-- Zero-or-more is expressed with `?` and produce an Option
prod Let: Expr = "let" ident:LIdent (":" tyIdent:Type)? "=" value:Expr "in" body:Expr
```
We thus get the following language fragments:

```
lang TupleExprAst
  syn Expr =
  | TupleExpr { fields : [Expr], info : Info }

  /- Some content omitted here -/
end

lang LetExprAst
  syn Expr =
  | LetExpr { ident: String, tyIdent: Option Type, value: Expr, body: Expr, info : Info }

  /- Some content omitted here -/
end
```

Note that `fields` is a sequence in `TupleExpr` and `tyIdent` is an
`Option Type` in `LetExpr`. More generally, if a field has type `X` in
the right-hand side of the production its type in the AST will depend
on how many types it _could_ appear in the production:

- If it must appear precisely once, then its type is merely `X`.
- If it can be absent or occur precisely once, then its type is
  `Option X`.
- Otherwise its type is `[X]`.

We can also give the constructor nested records using `{}`:

```
prod Match: Expr = "match" target:Expr "with" arms:{"|" pat:Pat "->" body:Expr}+
```

```
lang MatchExprAst
  syn Expr =
  | MatchExpr { target : Expr, arms : [{pat : Pat, body : Expr}], info : Info }
end
```

Explicit grouping (typically parentheses) should not be specified as a
production but rather explicitly as grouping:

```
grouping "(" Expr ")"
```

`grouping` declarations differ from normal productions in that they do
not affect the final AST; there is no node corresponding to
parentheses once parsing is complete.

### Precedence and Associativity

Precedence and associativity can disambiguate some expressions that
would otherwise be ambiguous, by dictating how expressions should
group in the absence of explicit grouping. This works largely as one
might expect from prior experience from math and most programming
languages; higher precedence operators "bind tighter", i.e., their AST
nodes are further from the root of the AST, and associativity
determines how expressions group between operators that have the same
precedence. However, there is one important difference: neither
precedence nor associativity is _mandatory_, you may leave some of
them undefined, which yields an ambiguous language. If this seems
perfectly reasonable to you, feel free to skip to the next heading,
which describes how to define precedence and associativity concretely.

Ambiguities arise almost immediately in most intuitively formulated
languages. In most programming languages these are resolved through
some mechanism in the parser that disambiguates according to some
convention, e.g., precedence and associativity. Other examples of
disambiguation mechanisms include longest match and various more
ad-hoc approaches.

A key term in the above paragraph is _convention_, these
disambiguations provide a good user interface if the programmer knows
the convention these disambiguations encode.

For precedence this implies a that, as a general rule of thumb, you
should give a defined precedence between two operators if _and only
if_ a typical user of your programming language can be expected to
know the precedence by heart. For example:

- Most people know the precedence of most arithmetic operators, `*`
  binds stronger than `+`, etc. Leaving precedence undefined would be
  tedious, since it would require a lot of parentheses.
- Most people know that comparators bind stronger than boolean and/or,
  i.e., that `a == b && c` means `(a == b) && c`, not `a == (b && c)`.
- Most mathematicians know that `a && b || c` is `(a && b) || c`, but
  it's not as obvious for many programmers. Relatively few expressions
  use both of these operators, thus we could leave precedence
  undefined (which ends up making the parentheses required) without
  introducing too much tedium.
  - However, it makes no sense to require parentheses for, e.g., `a &&
    b && c` since `&&` is associative (in the mathematical sense),
    thus its still useful to define an associativity here.
- Relatively few know the precedence of bitwise operators, e.g., what
  should `a & b == c` be? In C and its descendants it's `a & (b ==
  c)`, in Python its `(a & b) == c`.
- Set union and intersection do not have a precedence convention at
  all, thus no typical user of your language can be expected to know
  the precedence.

To show the effect of leaving precedence undefined, consider the case
where `&&` and `||` do not have a defined relative precedence. In this
case we find that the code `a || b && c` is ambiguous, at which point
our generated parser will present the following error message:

```
example:1:1: Parse error, this code is ambiguous:
  ( a || b ) && c
  a || ( b && c )
```

It is worth noting also that adding precedence between two operators
that previously didn't have precedence is a backwards-compatible
change: all previously valid programs are still valid and parse the
same. This means that it is safe try out a language with more
ambiguity, see how programmers end up wanting to use the language
constructs in practice, and then removing the ambiguity when it's
clear how it should be done.

#### Defining Precedence and Associativity

Associativity is defined on a production:

```
prod left Add: Expr = left:Expr "+" right:Expr
infix right And: Expr = "&&"
```

Note that an associativity declaration is only valid on an infix
production, i.e., one that is both left and right-recursive.

Precedence is defined with the `precedence` construct:

```
precedence {
  Negate;
  Mul Div;
  Add Sub;
}
```

Each line, terminated with `;`, defines a precedence level; all
operators on the same level have equal precedence, and all operators
on earlier (higher) levels have higher precedence than those on later
(lower) levels.

A language definition can have any number of precedence tables, as
long as no two tables disagree on any pair of operators. As a trivial
example, these two precedence tables conflict:

```
precedence {
  Add Sub;  -- Equal precedence
}
precedence {
  Add; -- Add has higher precedence
  Sub;
}
```

To make it easier to write tables that don't conflict we thus provide
two features to remove precedences from a table. The most direct and
flexible method is to provide an `except` list:

```
precedence {
  Mul Div;
  Add Sub;
  Modulus;
  Equal NotEqual LessThan GreaterThan;
} except {
  Modulus ? Mul Div Add Sub;
  Equal NotEqual LessThan GreaterThan ? Equal NotEqual LessThan GreaterThan;
}
```

A precedence table with an except list behaves like a normal table
except for the operators appearing on opposite sides of a `?` in the
`except` list. The table above does not define precedence between
`Modulus` and any of the other arithmetic operators (though `Modulus`
still has higher precedence than the comparators, and the other
arithmetic operators have their normal precedence relative each
other), nor does it define precedence between any of the comparators.

As a slightly less verbose option, you can also remove precedence
between all operators appearing on the same level by starting the
level with `~`, i.e., the above table could be written a bit more
succinctly as:

```
precedence {
  Mul Div;
  Add Sub;
  Modulus;
  ~ Equal NotEqual LessThan GreaterThan;
} except {
  Modulus ? Mul Div Add Sub;
}
```

### Lexing; custom tokens and whitespace

The lexing phase uses language fragments written in the style of
`WSACParser` and `TokenParser` in `stdlib/parser/lexer.mc`. The syntax
for specifying which such fragments should be included in the lexer is
not yet stable, but presently looks as follows:

```
--    v-- What's the name of the token when included in a regex?
token String {
  -- Which file should be included, i.e., where is the fragment defined?
  include: "parser/lexer.mc",
  -- Which language fragment contains the token?
  lang: StringTokenParser,
  -- What should the type be in the generated AST?
  type: String,
  -- How do we construct the token representation, to be put in the grammar?
  unitConstructor: StringRepr (),
  -- How do we construct the token representation if it is given an argument?
  constructor: lam str. error "The string token doesn't take an argument",
}
```

All of the fields are optional except `include` and `lang`. For
example, to include MExpr style line comments:

```
token {
  include: "lexer.mc";
  lang: LineCommentParser;
}
```

Note that there is no name between `token` and `{`, since we're not
actually defining a token, merely including a language fragment that
parses line tokens.
