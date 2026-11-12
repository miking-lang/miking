-- Scalar intrinsics.
mexpr
utest addi 1 2 with 3 in
utest subi 1 2 with negi 1 in
utest muli 3 4 with 12 in
utest negi 5 with negi 5 in

-- Integer division truncates towards zero, and modulo takes the sign of the
-- dividend. `Math.floor` would disagree with both on negative operands.
utest divi 7 2 with 3 in
utest divi (negi 7) 2 with negi 3 in
utest modi 7 2 with 1 in
utest modi (negi 7) 2 with negi 1 in

utest lti 1 2 with true in
utest gti 1 2 with false in
utest eqi 2 2 with true in
utest neqi 2 2 with false in
utest leqi 2 2 with true in
utest geqi 1 2 with false in

-- Shifts are JavaScript's, which are 32-bit, where the reference backend's are
-- 63-bit. Only results the two agree on are exercised here.
utest slli 2 5 with 64 in
utest slli (negi 1) 1 with negi 2 in
utest srli 4 2 with 1 in
utest srli 64 5 with 2 in
utest srai 4 2 with 1 in
utest srai (negi 8) 1 with negi 4 in

-- Floats share the `number` representation; `int2float` is a no-op.
utest addf 1.5 2.25 with 3.75 in
utest subf 5.0 1.5 with 3.5 in
utest mulf 2.0 3.5 with 7.0 in
utest divf 7.0 2.0 with 3.5 in
utest negf 1.5 with negf 1.5 in
utest floorfi (negf 1.5) with negi 2 in
utest ceilfi (negf 1.5) with negi 1 in
utest int2float 3 with 3.0 in
utest floorfi (int2float 3) with 3 in
utest ltf 1.0 2.0 with true in
utest geqf 2.0 2.0 with true in

-- OCaml rounds half away from zero; JS `Math.round` rounds half towards
-- +Infinity, so these two disagree without the runtime helper.
utest roundfi 0.5 with 1 in
utest roundfi (negf 0.5) with negi 1 in
utest roundfi 1.5 with 2 in
utest roundfi (negf 1.5) with negi 2 in

-- A Char is a one-character string, so `char2int` is a codepoint lookup.
utest char2int 'a' with 97 in
utest int2char 98 with 'b' in
utest char2int (int2char 98) with 98 in
utest eqc 'a' 'a' with true in
utest eqc 'a' 'b' with false in
()
