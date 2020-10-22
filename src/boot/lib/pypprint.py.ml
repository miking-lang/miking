open Ustring.Op
open Pyast
open Printf

let pprint = function
  | PyObject v ->
      us (sprintf "PyObject(%s)" (Py.Object.to_string v))
  | Pyimport ->
      us "pyimport"
  | Pyconvert ->
      us "pyconvert"
  | Pycall (None, None) ->
      us "pycall"
  | Pycall (Some v, None) ->
      us (sprintf "pycall(%s)" (Py.Object.to_string v))
  | Pycall (Some v, Some s) ->
      us (sprintf "pycall(%s, %s)" (Py.Object.to_string v) s)
  | PycallKw (None, None, None) ->
      us "pycallkw"
  | PycallKw (Some v, None, None) ->
      us (sprintf "pycallkw(%s)" (Py.Object.to_string v))
  | PycallKw (Some v, Some s, None) ->
      us (sprintf "pycallkw(%s, %s)" (Py.Object.to_string v) s)
  | PycallKw (Some v, Some s, Some argv) ->
      let argv_str =
        "["
        ^ String.concat ", "
            (Array.to_list (Array.map Py.Object.to_string argv))
        ^ "]"
      in
      us (sprintf "pycallkw(%s, %s, %s)" (Py.Object.to_string v) s argv_str)
  | _ ->
      failwith "Can't happen"
