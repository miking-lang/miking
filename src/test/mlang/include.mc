include "lib.mc"                 -- Simple include
include "deplib.mc"              -- Deep include
include "also_includes_lib.mc"   -- Ignore duplicate includes
include "subfolder/inclib.mc"    -- even when the paths look different
include "../mexpr/letlamif.mc"   -- Include from other directory
include "test::mexpr/reclets.mc" -- Include from namespace
                                 -- (test should point to /path/to/miking/test)
include "stdlib::common.mc"      -- Include from standard library explicitly
include "string.mc"              -- Include from standard library implicitly

let decon = lam x. match x with TestCon _ then "match" else "no match"
let double_bump = lam n. bump (bump n)

mexpr

utest decon (TestCon {}) with "match" in
utest alsoIncludeDecon (TestCon {}) with "match" in
utest depDecon (TestCon {}) with "match" in
utest subDecon (TestCon {}) with "match" in
utest bump 10 with 11 in
utest double_bump 10 with 12 in
utest triple_bump 10 with 13 in
utest the_answer with 42 in
utest apply bump 10 with 11 in
utest string2int "42" with 42 in
()
