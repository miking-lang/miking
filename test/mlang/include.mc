include "lib.mc"               -- Simple include
include "deplib.mc"            -- Deep include
include "also_includes_lib.mc" -- Ignore duplicate includes
include "../mexpr/letlamif.mc" -- Include from other directory
include "string.mc"            -- Include from standard library

let double_bump = lam n. bump (bump n)

mexpr

utest bump 10 with 11 in
utest double_bump 10 with 12 in
utest triple_bump 10 with 13 in
utest the_answer with 42 in
utest string2int "42" with 42 in
utest map bump [1,2,3] with [2,3,4] in -- prelude is included automatically
()
