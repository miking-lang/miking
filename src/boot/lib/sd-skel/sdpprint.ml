open Sdast
open Ustring.Op

let pprint = function
  | EApp _ -> us "eapp"
