-- Functions related to the built-in symbol functionality (gensym, eqs, and
-- sym2int)

include "string.mc"

-- 'sym2string sym' returns a string corresponding to the symbol 'sym'. This
-- exposes the underlying symbol representation, but can be useful in many
-- cases.
let sym2string = lam s. int2string (sym2int s)
