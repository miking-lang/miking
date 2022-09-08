include "javascript/web/dom-api-ext.mc"

include "string.mc"

mexpr

let doc = getDocument () in
match doc with { location = { hostname = hostname }} in
-- let hostname = doc.location.hostname in
utest eqString hostname "" with false in

()
