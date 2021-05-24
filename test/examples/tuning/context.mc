include "string.mc"
include "common.mc"

let foo = lam n.
  let h1 = HoleBool {default = true, depth = 1} in
  let h2 = HoleBool {default = true, depth = 1} in
  printLn (join ["Value of h1 ", if h1 then "true" else "false", "\n"]);
  printLn (join ["Value of h2 ", if h2 then "true" else "false", "\n"]);
  printLn (join ["Value of n ", int2string n, "\n"]);
  if eqi n 0 then
    sleepMs (if and h1 h2 then 1000 else
             if and h1 (not h2) then 500 else
             if and (not h1) h2 then 0
             else 200)
  else
    sleepMs (if and h1 h2 then 20 else
             if and h1 (not h2) then 60 else
             if and (not h1) h2 then 11
             else 10)

mexpr
foo 0;
foo 1
