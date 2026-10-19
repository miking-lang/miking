-- Scalar intrinsics.
--
-- Every value printed here is an integer. `dprint` renders bools, chars and
-- floats differently in the OCaml backend than anywhere else -- bools print as
-- 1/0, chars as codepoints, and 1.0 as "1." -- so results of those types are
-- reduced to integers rather than printed directly.
mexpr
dprint (addi 1 2);
dprint (subi 1 2);
dprint (muli 3 4);
dprint (negi 5);

-- Integer division truncates towards zero, and modulo takes the sign of the
-- dividend. `Math.floor` would disagree with both on negative operands.
dprint (divi 7 2);
dprint (divi (negi 7) 2);
dprint (modi 7 2);
dprint (modi (negi 7) 2);

dprint (if lti 1 2 then 1 else 0);
dprint (if gti 1 2 then 1 else 0);
dprint (if eqi 2 2 then 1 else 0);
dprint (if neqi 2 2 then 1 else 0);
dprint (if leqi 2 2 then 1 else 0);
dprint (if geqi 1 2 then 1 else 0);

-- Shifts use OCaml's 63-bit semantics. Only results inside 2^53 are printed;
-- anything wider cannot be represented as a JS number and raises instead.
dprint (slli 2 5);
dprint (slli (negi 1) 1);
dprint (srli 4 2);
dprint (srli 64 5);
dprint (srai 4 2);
dprint (srai (negi 8) 1);

-- Floats share the `number` representation; `int2float` is a no-op.
dprint (floorfi (addf 1.5 2.25));
dprint (floorfi (subf 5.0 1.5));
dprint (floorfi (mulf 2.0 3.5));
dprint (floorfi (divf 7.0 2.0));
dprint (floorfi (negf 1.5));
dprint (ceilfi (negf 1.5));
-- NOTE: `ceilfi (negf 0.2)` and friends land on JS negative zero, which this
-- backend accepts as an alternative encoding of the Int 0. `dprint` is the one
-- thing that can see the difference, and its format is unspecified, so those
-- cases are deliberately not exercised here.
dprint (floorfi (int2float 3));
dprint (if ltf 1.0 2.0 then 1 else 0);
dprint (if geqf 2.0 2.0 then 1 else 0);

-- OCaml rounds half away from zero; JS `Math.round` rounds half towards
-- +Infinity, so these two disagree without the runtime helper.
dprint (roundfi 0.5);
dprint (roundfi (negf 0.5));
dprint (roundfi 1.5);
dprint (roundfi (negf 1.5));

-- A Char is a one-character string, so `char2int` is a codepoint lookup.
dprint (char2int 'a');
dprint (char2int (int2char 98));
dprint (if eqc 'a' 'a' then 1 else 0);
dprint (if eqc 'a' 'b' then 1 else 0)
