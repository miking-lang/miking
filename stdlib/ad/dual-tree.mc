-- This is an implementation of the tree-based dual-number API described in the
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearlmutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Functions part of the API are prefixed with dual. Other functions are
-- internal.

include "math.mc"
include "string.mc"

type Eps = Int

-- Dual's can be nested and are implemented as explicit trees.
type Dual a
con Dual : all a. {e : Eps, x : Dual a, xp : Dual a} -> Dual a
con Primal : all a. a -> Dual a

-- Epsilons are ordered.
let dualLtE : Eps -> Eps -> Bool = lti
let dualEqE : Eps -> Eps -> Bool = eqi

-- false if x' = 0 in x+ex'
let dualIsDual : all a. Dual a -> Bool =
lam n.
  switch n
  case Primal _ then false
  case Dual _ then true
  end

-- x if x' = 0 otherwise x+ex'
let dualCreateDual : all a. (a -> Bool) -> Eps -> Dual a -> Dual a -> Dual a =
lam isZero. lam e. lam x. lam xp.
  match xp with Primal v then
    if isZero v then x else Dual { e = e, x = x, xp = xp }
  else Dual { e = e, x = x, xp = xp }

-- e in x+ex'
let dualEpsilon : all a. Dual a -> Eps =
lam n.
  match n with Dual dn then dn.e
  else error "Operand not a dual number"

-- x in x+ex' given e
let dualPrimal : all a. Eps -> Dual a -> Dual a =
lam e. lam n.
  switch n
  case Primal _ then n
  case Dual dn then if dualLtE dn.e e then n else dn.x
  end

-- x in x+e1(x+e2(x+e3(...)))
recursive
let dualPrimalDeep : all a. Dual a -> a =
lam n.
  switch n
  case Primal n then n
  case Dual {x = x} then dualPrimalDeep x
  end
end

-- x' in x+ex' given e
let dualPertubation : all a. a -> Eps -> Dual a -> Dual a =
lam zero. lam e. lam n.
  switch n
  case Primal _ then Primal zero
  case Dual dn then if dualLtE dn.e e then Primal zero else dn.xp
  end

-- generate a unique epsilon e1 that fulfills the invariant e1 > e for all
-- previously generated epsilons e.
let e = ref 0
let dualGenEpsilon : () -> Eps =
lam. modref e (succ (deref e)); deref e

-- Structural equality function for duals
let dualEq : all a. (a -> a -> Bool) -> Dual a -> Dual a -> Bool =
  lam eq.
  recursive let recur = lam n1. lam n2.
    switch (n1, n2)
    case (Primal r1, Primal r2) then eq r1 r2
    case (Dual {e = e1, x = x1, xp = xp1}, Dual {e = e2, x = x2, xp = xp2}) then
      if dualEqE e1 e2 then
        if recur x1 x2 then recur xp1 xp2 else false
      else false
    case (_, _) then false
    end
  in recur

-- String representation of duals
let dualToString : all a. (a -> String) -> Dual a -> String =
lam pri2str. lam n.
  let wrapInParen = lam n. lam str.
    if dualIsDual n then join ["(", str, ")"] else str
  in
  recursive let recur = lam n.
    match n with Primal r then pri2str r
    else match n with Dual {e = e, x = x, xp = xp} then
      join [
        wrapInParen x (recur x),
        " + e",
        int2string e,
        " ",
        wrapInParen xp (recur xp)
      ]
    else never
  in recur n
