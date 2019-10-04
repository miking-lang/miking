
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   boot.ml is the main entry point for first stage of the
   bootstrapped Miking compiler. The bootstapper is interpreted and
   implemented in OCaml. Note that the Miking bootstrapper
   only implements a subset of the Ragnar language.
*)


open Ustring.Op
open Printf
open Ast
open Msg
open Mexpr
open Pprint

let prog_argv = ref []          (* Argv for the program that is executed *)


(* Debug template function. Used below *)
let debug_after_parse t =
  if enable_debug_after_parse then
    (printf "\n-- After parsing --  \n";
     uprint_endline (pprintML t);
     t)
  else t


(* Debug template function. Used below *)
let debug_after_debruijn t =
  if enable_debug_after_debruijn  then
    (printf "\n-- After debruijn --  \n";
     uprint_endline (pprintME t);
     t)
  else t



(* Main function for evaluation a function. Performs lexing, parsing
   and evaluation. Does not perform any type checking *)
let evalprog filename  =
  if !utest then printf "%s: " filename;
  utest_fail_local := 0;
  let fs1 = open_in filename in
  let tablength = 8 in
  begin try
    Lexer.init (us filename) tablength;
    let parsed =
      fs1 |> Ustring.lexing_from_channel
          |> Parser.main Lexer.main |> debug_after_parse in
    (parsed
     |> Mlang.translate
     |> Mexpr.debruijn (builtin |> List.split |> fst |> (List.map (fun x-> VarTm(us x))))
     |> debug_after_debruijn
     |> eval (builtin |> List.split |> snd |> List.map (fun x -> TmConst(NoInfo,x)))
     |> fun _ -> ())
    with
    | Lexer.Lex_error m ->
      if !utest then (
        printf "\n%s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Error m ->
      if !utest then (
        printf "\n%s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Parsing.Parse_error ->
      if !utest then (
        printf "\n%s" (Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())))
  end; close_in fs1;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n"


(* Define the file slash, to make it platform independent *)
let sl = if Sys.win32 then "\\" else "/"

(* Add a slash at the end "\\" or "/" if not already available *)
let add_slash s =
  if String.length s = 0 || (String.sub s (String.length s - 1) 1) <> sl
  then s ^ sl else s

(* Expand a list of files and folders into a list of file names *)
let files_of_folders lst = List.fold_left (fun a v ->
  if Sys.is_directory v then
    (Sys.readdir v
        |> Array.to_list
        |> List.filter (fun x -> not (String.length x >= 1 && String.get x 0 = '.'))
        |> List.map (fun x -> (add_slash v) ^ x)
        |> List.filter (fun x -> not (Sys.is_directory x))
        |> List.filter (fun x -> not (String.contains x '#' || String.contains x '~'))
    ) @ a
  else v::a
) [] lst

(* Iterate over all potential test files and run tests *)
let testprog lst =
    utest := true;
    (* Select the lexer and parser, depending on the DSL*)
    let eprog name = evalprog name in
    (* Evaluate each of the programs in turn *)
    List.iter eprog (files_of_folders lst);

    (* Print out unit test results, if applicable *)
    if !utest_fail = 0 then
      printf "Unit testing SUCCESSFUL after executing %d tests.\n\n"
        (!utest_ok)
            else
      printf "ERROR! %d successful tests and %d failed tests.\n\n"
        (!utest_ok) (!utest_fail)

(* Run program *)
let runprog name lst =
    prog_argv := lst;
    evalprog name


(* Print out main menu *)
let menu() =
  printf "Usage: boot [run|test] <files>\n";
  printf "\n"


(* Main function. Checks arguments and reads file names *)
let main =
  (* Check command  *)
  (match Array.to_list Sys.argv |> List.tl with

  (* Run tests on one or more files *)
  | "test"::lst | "t"::lst -> testprog lst

  (* Run one program with program arguments without typechecking *)
  | "run"::name::lst | name::lst -> runprog name lst

  (* Show the menu *)
  | _ -> menu())
