(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ustring.Op
open Printf
open Ast
open Msg
open Mexpr
open Parserutils
open Ustring

let add_prelude = function
  | Program (includes, tops, tm) ->
      Program (default_includes @ includes, tops, tm)

let error_to_ustring e =
  match e with
  | Lexer.Lex_error m ->
      message2str m
  | Parsing.Parse_error ->
      message2str (Lexer.parse_error_message ())
  | Error m ->
      message2str m
  | _ ->
      us (Printexc.to_string e)

(* Main function for evaluating a program. Performs lexing, parsing
   and evaluation. Does not perform any type checking *)
let evalprog filename =
  (* Make sure the filename is an absolute path, otherwise the duplicate file detection won't work *)
  let filename =
    if Filename.is_relative filename then
      Filename.concat (Sys.getcwd ()) filename
    else filename
  in
  if !utest then printf "%s: " filename ;
  utest_fail_local := 0 ;
  ( try
      let parsed = parse_mcore_file filename in
      parsed |> add_prelude
      |> merge_includes (Filename.dirname filename) [filename]
      |> Mlang.flatten |> Mlang.desugar_post_flatten |> debug_after_mlang
      |> Mexpr.symbolize builtin_name2sym
      |> debug_after_symbolize
      |> Mexpr.eval builtin_sym2term
      |> fun _ -> ()
    with (Lexer.Lex_error _ | Error _ | Parsing.Parse_error) as e ->
      let error_string = Ustring.to_utf8 (error_to_ustring e) in
      if !utest then (
        printf "\n%s" error_string ;
        utest_fail := !utest_fail + 1 ;
        utest_fail_local := !utest_fail_local + 1 )
      else fprintf stderr "%s\n" error_string ) ;
  parsed_files := [] ;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n" ;
  if !enable_debug_profiling then
    Hashtbl.iter
      (fun k (c, t) ->
        printf "%s: %d call%s, %f ms\n"
          (k |> info2str |> to_utf8)
          c
          (if c == 1 then "" else "s")
          t)
      runtimes
  else ()
