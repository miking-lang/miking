
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
 *)


open Ast
open Pyast
open Pypprint
open Ustring.Op
open Msg

let mk_py fi p = TmConst(fi, CPy(p))

let externals =
  let f p = mk_py NoInfo p in
  [("pycall", f(Pycall(None,None))); ("pyimport", f(Pyimport))]

let arity = function
  | PyObject(_) -> 0
  | Pyimport -> 1
  | Pycall(None, None) -> 3 | Pycall(Some(_),None) -> 2 | Pycall(_,Some(_)) -> 1

let rec val_to_python fi = function
  | TmConst(_,CBool(v)) -> Py.Bool.of_bool v
  | TmConst(_,CInt(v)) -> Py.Int.of_int v
  | TmConst(_,CFloat(v)) -> Py.Float.of_float v
  | TmConst(_,CPy(PyObject(v))) -> v
  | TmSeq(_,s) ->
    begin
      try tmseq2ustring fi s |> Ustring.to_utf8 |> Py.String.of_string
      with _ -> Mseq.to_list s |> Py.List.of_list_map (val_to_python fi)
    end
  (* | TmRecord(_,r1) ->
     | TmConapp(_,_,sym1,v1) -> *)
  | _ -> raise_error fi "The supplied value cannot be used as a python argument"

let fail_constapp f v fi = raise_error fi
                          ("Incorrect application. function: "
                           ^ Ustring.to_utf8 (pprint f)
                           ^ " value: "
                           ^ Ustring.to_utf8
                              (Pprint.ustring_of_tm v))

let initialize_on_first_call () =
  if not (Py.is_initialized ()) then
    Py.initialize ~version:3 ()

let delta _ _ fi c v =
  initialize_on_first_call ();
  let fail_constapp fi = fail_constapp c v fi in
  match c,v with
    | PyObject(_),_ -> fail_constapp fi
    | Pyimport, TmSeq(fi, lst) ->
        mk_py fi (PyObject(Py.import (tmseq2ustring fi lst |> Ustring.to_utf8)))
    | Pyimport,_ -> fail_constapp fi
    | Pycall(None, None),TmConst(_,CPy(PyObject(obj))) -> mk_py fi (Pycall(Some(obj), None))
    | Pycall(None, None),_ -> fail_constapp fi
    | Pycall(Some(m), None),TmSeq(fi,lst) ->
        mk_py fi (Pycall(Some(m), Some(tmseq2ustring fi lst |> Ustring.to_utf8)))
    | Pycall(Some(_), None),_ -> fail_constapp fi
    | Pycall(Some(m),Some(s)),TmRecord(fi,args) ->
        let size_of_record = Record.cardinal args in
        let argv = Array.make size_of_record (Py.Float.of_float 0.) in
        Record.iter (fun k v -> Array.set argv (int_of_ustring k) (val_to_python fi v)) args;
        mk_py fi (PyObject(Py.Module.get_function m s argv))
    | Pycall(_, _), _ -> fail_constapp fi
