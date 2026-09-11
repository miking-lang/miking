-- Scanning a string, which in MCore is a sequence of characters.
--
-- Exercises: `int2char`, `char2int` and `eqc` over a character sequence, plus
-- `get` and `reverse` on one.  Character literals in the comparison also make
-- this the only benchmark that reaches the evaluator's character values.
--
-- Scales linearly in `scale` (string length).

mexpr

let scale = 1200000 in -- SCALE

let s = create scale (lam i. int2char (addi 97 (modi (muli i 7) 26))) in
let r = reverse s in

-- The mirror check is capped so that it stays in bounds at any scale.
let m = if lti scale 2048 then scale else 2048 in

recursive let scan = lam i. lam acc.
  if geqi i scale then acc
  else
    let c = get s i in
    scan (addi i 1)
      (if eqc c 'a' then addi acc 1
       else if eqc c 'e' then addi acc 1
       else if geqi (char2int c) 117 then addi acc 2
       else acc)
in

recursive let mirror = lam i. lam acc.
  if geqi i m then acc
  else
    let j = subi (subi scale 1) i in
    mirror (addi i 1) (if eqc (get s i) (get r j) then addi acc 1 else acc)
in

exit (modi (addi (scan 0 0) (mirror 0 0)) 251)
