include "docgen/docgen.mc"
include "options-type.mc"

let docgen = lam files. lam options : Options. lam.
    docgen { options.docgenOptions with files = files }
