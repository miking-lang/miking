include "docgen/docgen.mc"

let docgen = lam files. lam options : Options. lam.
    match files with [f] ++ _ then
          docgen { options.docgenOptions with file = f }
    else ()
