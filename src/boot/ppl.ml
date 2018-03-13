
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   The main experiment platform for probabilitic programming.
   Main contributer: Daniel Lunden
*)

open Utils
open Ustring.Op
open Printf
open Ast
open Msg




(* Main function for the evaluation of a probabilitic program *)
let evalprog debruijn eval builtin filename =
  if !utest then printf "%s: " filename;
  utest_fail_local := 0;
  let fs1 = open_in filename in
  let tablength = 8 in
  begin try
    Ppllexer.init (us filename) tablength;
    fs1 |> Ustring.lexing_from_channel
        |> Pplparser.main Ppllexer.main
        |> debruijn (builtin |> List.split |> fst |> List.map us)
        |> eval (builtin |> List.split |> snd |> List.map (fun x -> TmConst(NoInfo,x)))
        |> fun _ -> ()

    with
    | Ppllexer.Lex_error m ->
      if !utest then (
        printf "\n ** %s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Error m ->
      if !utest then (
        printf "\n ** %s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Parsing.Parse_error ->
      if !utest then (
        printf "\n ** %s" (Ustring.to_utf8 (Msg.message2str (Ppllexer.parse_error_message())));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str (Ppllexer.parse_error_message())))
  end; close_in fs1;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n"
