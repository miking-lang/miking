include "string.mc"
include "name.mc"

let name2str = lam n.
    match nameGetSym n with Some s
        then concat (nameGetStr n) (int2string (sym2hash s))
        else nameGetStr n