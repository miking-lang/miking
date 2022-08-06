include "javascript/web/dom-api-ext.mc"

include "string.mc"

mexpr

let doc = getDocument () in
let hostname = doc.location.hostname in
utest eqString hostname "" with false in

()
