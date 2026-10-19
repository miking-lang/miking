-- Constructors, recursion and tail calls.
--
-- With `recursive let` supported, `int2string` compiles, so this is the first
-- test able to print integers directly rather than reducing them to digits.
include "common.mc"
include "seq.mc"
include "string.mc"

type Shape
con Circle : Float -> Shape
con Rect : (Float, Float) -> Shape
con Empty : () -> Shape

mexpr

-- Self tail recursion. 100000 frames would overflow the JS stack if this
-- compiled to actual recursion, so this also checks the loop rewrite.
recursive
  let sumTo = lam n. lam acc.
    if lti n 1 then acc else sumTo (subi n 1) (addi acc n)
in
printLn (int2string (sumTo 10 0));
printLn (int2string (sumTo 100000 0));

-- The arguments must be rebound simultaneously: `next` is computed from the
-- old `n`, so rebinding one parameter at a time would give a different answer.
recursive
  let shifted = lam n. lam acc.
    if eqi n 0 then acc else shifted (subi n 1) (muli acc n)
in
printLn (int2string (shifted 5 1));

-- Mutual recursion, which relies on JS hoisting function declarations.
--
-- NOTE: only *self* tail calls become loops. A tail call to another function
-- in the same group is still a call and consumes stack, so the depth here is
-- deliberately small.
recursive
  let isEven = lam n. if eqi n 0 then true else isOdd (subi n 1)
  let isOdd = lam n. if eqi n 0 then false else isEven (subi n 1)
in
printLn (if isEven 10 then "even" else "odd");
printLn (if isEven 7 then "even" else "odd");
printLn (if isOdd 999 then "odd" else "even");

-- Recursion that is not in tail position still works, it just uses the stack.
recursive
  let len = lam xs. match xs with [] then 0 else addi 1 (len (tail xs))
in
printLn (int2string (len [1, 2, 3, 4]));

-- Constructors.
let area = lam s.
  match s with Circle r then mulf r r
  else match s with Rect d then mulf d.0 d.1
  else 0.0
in
printLn (float2string (area (Circle 3.0)));
printLn (float2string (area (Rect (2.0, 4.0))));
printLn (float2string (area (Empty ())));

-- A constructor value flowing through a recursive function.
recursive
  let total = lam shapes. lam acc.
    match shapes with [] then acc
    else total (tail shapes) (addf acc (area (head shapes)))
in
printLn (float2string (total [Circle 1.0, Rect (3.0, 3.0), Empty ()] 0.0));

-- Strings now come from the standard library rather than a local helper.
printLn (join ["a", "b", "c"]);
printLn (strJoin "," ["x", "y", "z"]);
printLn (int2string (length "hello"));
printLn (if eqString "ab" "ab" then "eq" else "ne")
