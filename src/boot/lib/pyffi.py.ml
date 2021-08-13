(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast
open Pyast
open Pypprint
open Ustring.Op
open Msg
open Intrinsics

let mk_py fi p = TmConst (fi, CPy p)

let externals =
  let f p = mk_py NoInfo p in
  [ ("pycall", f (Pycall (None, None)))
  ; ("pycallkw", f (PycallKw (None, None, None)))
  ; ("pyimport", f Pyimport)
  ; ("pyconvert", f Pyconvert) ]

let arity = function
  | PyObject _ ->
      0
  | Pyimport ->
      1
  | Pyconvert ->
      1
  | Pycall (None, None) ->
      3
  | Pycall (Some _, None) ->
      2
  | Pycall (_, Some _) ->
      1
  | PycallKw (None, None, None) ->
      4
  | PycallKw (Some _, None, None) ->
      3
  | PycallKw (_, Some _, None) ->
      2
  | PycallKw (_, _, Some _) ->
      1

let rec val_to_python fi = function
  | TmConst (_, CBool v) ->
      Py.Bool.of_bool v
  | TmConst (_, CInt v) ->
      Py.Int.of_int v
  | TmConst (_, CFloat v) ->
      Py.Float.of_float v
  | TmConst (_, CPy (PyObject v)) ->
      v
  | TmSeq (_, s) -> (
    try tmseq2ustring fi s |> Ustring.to_utf8 |> Py.String.of_string
    with _ ->
      Mseq.Helpers.to_list s |> Py.List.of_list_map (val_to_python fi) )
  | TmRecord (_, r) when r = Record.empty ->
      Py.none
  | TmRecord (_, r) -> (
    match record2tuple r with
    | Some tms ->
        Py.Tuple.of_list_map (val_to_python fi) (List.rev tms)
    | None ->
        Py.Dict.of_bindings_map
          (fun x -> Py.String.of_string (Ustring.to_utf8 x))
          (val_to_python fi) (Record.bindings r) )
  | _ ->
      raise_error fi "The supplied value cannot be used as a python argument"

let val_to_string fi = function
  | TmSeq (_, s) -> (
    try tmseq2ustring fi s |> Ustring.to_utf8
    with _ ->
      raise_error fi "The supplied sequence cannot be used as a string" )
  | _ ->
      raise_error fi "The supplied value is not a string"

let rec python_to_val fi obj =
  match Py.Type.get obj with
  | Py.Type.Bool ->
      TmConst (fi, CBool (Py.Bool.to_bool obj))
  | Py.Type.Int ->
      TmConst (fi, CInt (Py.Int.to_int obj))
  | Py.Type.Long ->
      TmConst (fi, CInt (Py.Long.to_int obj))
  | Py.Type.Float ->
      TmConst (fi, CFloat (Py.Float.to_float obj))
  | Py.Type.None ->
      TmRecord (fi, Record.empty)
  | Py.Type.Bytes | Py.Type.Unicode ->
      let ustr = us (Py.String.to_string obj) in
      TmSeq (fi, ustring2tmseq fi ustr)
  | Py.Type.List ->
      let lst = Py.List.to_list_map (python_to_val fi) obj in
      TmSeq (fi, Mseq.Helpers.of_list lst)
  | Py.Type.Tuple ->
      let lst = Py.Tuple.to_list_map (python_to_val fi) obj in
      tuple2record fi lst
  | Py.Type.Dict ->
      let bindings = Py.Dict.to_bindings_string obj in
      let mcore_bindings =
        List.map (fun (k, v) -> (us k, python_to_val fi v)) bindings
      in
      let record =
        List.fold_right
          (fun (k, v) r -> Record.add k v r)
          mcore_bindings Record.empty
      in
      TmRecord (fi, record)
  | t ->
      raise_error fi
        ( "The supplied python value with type " ^ Py.Type.name t
        ^ " cannot be converted to an MCore value" )

let is_none = function PyObject v -> v = Py.none | _ -> false

let fail_constapp f v fi =
  raise_error fi
    ( "Incorrect application. function: "
    ^ Ustring.to_utf8 (pprint f)
    ^ " value: "
    ^ Ustring.to_utf8 (Pprint.ustring_of_tm v) )

let initialize_on_first_call () =
  if not (Py.is_initialized ()) then Py.initialize ~version:3 ()

let delta _ fi c v =
  initialize_on_first_call () ;
  let fail_constapp fi = fail_constapp c v fi in
  match (c, v) with
  | PyObject _, _ ->
      fail_constapp fi
  | Pyimport, TmSeq (fi, lst) ->
      mk_py fi (PyObject (Py.import (tmseq2ustring fi lst |> Ustring.to_utf8)))
  | Pyimport, _ ->
      fail_constapp fi
  | Pyconvert, TmConst (fi, CPy (PyObject obj)) ->
      python_to_val fi obj
  | Pyconvert, _ ->
      fail_constapp fi
  | Pycall (None, None), TmConst (_, CPy (PyObject obj)) ->
      mk_py fi (Pycall (Some obj, None))
  | Pycall (None, None), _ ->
      fail_constapp fi
  | Pycall (Some m, None), TmSeq (fi, lst) ->
      mk_py fi (Pycall (Some m, Some (tmseq2ustring fi lst |> Ustring.to_utf8)))
  | Pycall (Some _, None), _ ->
      fail_constapp fi
  | Pycall (Some m, Some s), TmRecord (fi, args) ->
      let size_of_record = Record.cardinal args in
      let argv = Array.make size_of_record (Py.Float.of_float 0.) in
      Record.iter
        (fun k v -> argv.(int_of_ustring k) <- val_to_python fi v)
        args ;
      mk_py fi (PyObject (Py.Module.get_function m s argv))
  | Pycall (_, _), _ ->
      fail_constapp fi
  | PycallKw (None, None, None), TmConst (_, CPy (PyObject obj)) ->
      mk_py fi (PycallKw (Some obj, None, None))
  | PycallKw (None, None, None), _ ->
      fail_constapp fi
  | PycallKw (Some m, None, None), TmSeq (fi, lst) ->
      mk_py fi
        (PycallKw (Some m, Some (tmseq2ustring fi lst |> Ustring.to_utf8), None)
        )
  | PycallKw (Some _, None, None), _ ->
      fail_constapp fi
  | PycallKw (Some m, Some s, None), TmRecord (fi, args) ->
      let size_of_record = Record.cardinal args in
      let argv = Array.make size_of_record (Py.Float.of_float 0.) in
      Record.iter
        (fun k v -> argv.(int_of_ustring k) <- val_to_python fi v)
        args ;
      mk_py fi (PycallKw (Some m, Some s, Some argv))
  | PycallKw (Some m, Some s, Some a), TmRecord (fi, args) ->
      let kwargs =
        List.map
          (fun (k, v) -> (Ustring.to_utf8 k, val_to_python fi v))
          (Record.bindings args)
      in
      mk_py fi (PyObject (Py.Module.get_function_with_keywords m s a kwargs))
  | PycallKw (_, _, _), _ ->
      fail_constapp fi
