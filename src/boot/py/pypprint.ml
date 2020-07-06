open Ustring.Op
open Pyast

let pprint = function
  | PyObject(_) -> us "PyObject"
  | Pyimport -> us "pyimport"
  | Pycall(None,None) -> us "pycall"
  | Pycall(Some(_),None) -> us "pycall PyObject"
  | Pycall(Some(_),Some s) -> us "pycall PyObject " ^. us s
  | _ -> failwith "Can't happen"
