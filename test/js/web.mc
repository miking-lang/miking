include "javascript/web/dom-api-ext.mc"

include "string.mc"

mexpr

let doc = getDocument () in
utest eqString doc.location.hostname "" with false in

()
