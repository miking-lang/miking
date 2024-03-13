(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Printf
open Ast
open Mexpr
open Msg
open Parserutils
open Ustring
open Builtin

(* Main function for evaluating a program. Performs lexing, parsing
   and evaluation. Does not perform any type checking *)
let evalprog filename =
  (* Make sure the filename is an absolute path, otherwise the duplicate file detection won't work *)
  let filename = Utils.normalize_path filename in
  if !utest then printf "%s: " filename ;
  utest_fail_local := 0 ;
  ( try
      filename |> parse_mcore_file |> Mlang.translate_program
      |> debug_after_mlang |> raise_parse_error_on_non_unique_external_id
      |> (fun t -> if !utest then t else remove_all_utests t)
      |> Symbolize.symbolize builtin_name2sym
      |> debug_after_symbolize
      |> raise_parse_error_on_partially_applied_external
      |> Deadcode.elimination builtin_sym2term builtin_name2sym []
      |> prune_external_utests_boot |> debug_after_pruning_external_utests
      |> Deadcode.elimination builtin_sym2term builtin_name2sym []
      |> debug_after_dead_code_elimination
      |> Mexpr.scan builtin_sym2term
      |> Mexpr.eval builtin_sym2term pe_init
      |> fun _ -> ()
    with (Lexer.Lex_error _ | Error _ | Parser.Error) as e ->
      let error_string = Ustring.to_utf8 (error_to_ustring e) in
      if !utest then (
        printf "\n%s" error_string ;
        utest_fail := !utest_fail + 1 ;
        utest_fail_local := !utest_fail_local + 1 )
      else fprintf stderr "%s\n" error_string ;
      exit 1 ) ;
  if !utest && !utest_fail_local = 0 then printf " OK\n" ;
  if !enable_debug_profiling then
    let bindings =
      Hashtbl.fold (fun k v acc -> (k, v) :: acc) runtimes []
      |> List.sort (fun (_, (_, t1)) (_, (_, t2)) -> Float.compare t1 t2)
      |> List.rev
    in
    List.iter
      (fun (info, (count, ms)) ->
        printf "%s: %d call%s, %f ms\n"
          (info |> info2str |> to_utf8)
          count
          (if count == 1 then "" else "s")
          ms )
      bindings
  else ()
