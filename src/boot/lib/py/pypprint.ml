open Ustring.Op
open Pyast
open Printf

let pprint = function
  | PyObject(v) -> us (sprintf "PyObject(%s)" (Py.Object.to_string v))
  | Pyimport -> us "pyimport"
  | Pyconvert -> us "pyconvert"
  | Pycall(None,None) -> us "pycall"
  | Pycall(Some(v),None) -> us (sprintf "pycall(%s)" (Py.Object.to_string v))
  | Pycall(Some(v),Some s) -> us (sprintf "pycall(%s, %s)" (Py.Object.to_string v) s)
  | _ -> failwith "Can't happen"
