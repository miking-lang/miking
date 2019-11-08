include "lib.mc"               -- Simple include
include "deplib.mc"            -- Deep include
include "also_includes_lib.mc" -- Ignore duplicate includes
include "../mexpr/letlamif.mc" -- Include from other directory

let double_bump = lam n. bump (bump n)

main

utest bump 10 with 11 in
utest double_bump 10 with 12 in
utest triple_bump 10 with 13 in
utest the_answer with 42 in
()