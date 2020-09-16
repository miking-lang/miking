open Extast
open Ustring.Op

let pprint = function
  (* Elementary functions *)
  | Esin -> us "extSin"
  | Ecos -> us "extCos"
  | Eatan -> us"extAtan"
  | Eexp -> us"extExp"
