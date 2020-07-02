
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

module Option = BatOption

(* Standard lib default local path on unix (used by make install) *)
let stdlib_loc_unix =
  match Sys.getenv_opt "HOME" with
  | Some home -> home ^ "/.local/lib/mcore/stdlib"
  | None -> "@@@"

let stdlib_loc =
  match Sys.getenv_opt "MCORE_STDLIB" with
  | Some path -> path
  | None ->
    if Sys.os_type = "Unix" &&
       Sys.file_exists stdlib_loc_unix
    then stdlib_loc_unix
    else "@@@"

let default_includes =
  let prelude = [Include(NoInfo, us"prelude.mc")] in
  match Sys.getenv_opt "MCORE_STDLIB" with
  | Some "@@@" -> [] (* Needed for test of stdlib *)
  | Some _ -> prelude
  | None ->
    if Sys.os_type = "Unix" &&
       Sys.file_exists stdlib_loc_unix
    then prelude
    else []

let prog_argv = ref []          (* Argv for the program that is executed *)

(* Debug printing after parse*)
let debug_after_parse t =
  if !enable_debug_after_parse then
    (printf "\n-- After parsing (only mexpr part) --\n";
     uprint_endline (ustring_of_program t);
     t)
  else t

(* Debug printing after symbolize transformation *)
let debug_after_symbolize t =
  if !enable_debug_after_symbolize then
    (printf "\n-- After symbolize --\n";
     uprint_endline (ustring_of_tm ~margin:80 t);
     t)
  else t

(* Debug mlang to mexpr transform *)
let debug_after_mlang t =
  if !enable_debug_after_mlang then
    (printf "\n-- After mlang --\n";
     uprint_endline (ustring_of_tm ~margin:80 t);
     t)
  else t

(* Keep track of which files have been parsed to avoid double includes *)
let parsed_files = ref []
let tablength = 8

(* Open a file and parse it into an MCore program *)
let parse_mcore_file filename =
  let fs1 = open_in filename in
  let p =
    Lexer.init (us filename) tablength;
    fs1 |> Ustring.lexing_from_channel
    |> Parser.main Lexer.main |> debug_after_parse
  in
  close_in fs1; (parsed_files := filename::!parsed_files); p

(* Parse and merge all files included from a program, given the
   path of the "root program". Raise an error if a loop is
   detected. *)
let rec merge_includes root visited = function
  | Program(includes, tops, tm) ->
     let rec parse_include root = function
       | Include(info, path) as inc ->
          let filename = Filename.concat root (Ustring.to_utf8 path) |> Utils.normalize_path in
          if List.mem filename visited
          then raise_error info ("Cycle detected in included files: " ^ filename)
          else if List.mem filename !parsed_files
          then None (* File already included *)
          else
            if Sys.file_exists filename then
              parse_mcore_file filename |>
              merge_includes (Filename.dirname filename) (filename::visited) |>
              Option.some
            else if root != stdlib_loc &&
                    Sys.file_exists @@
                      Filename.concat stdlib_loc (Ustring.to_utf8 path)
            then parse_include stdlib_loc inc
            else raise_error info ("No such file: \"" ^ filename ^ "\"")
     in
     let included =
       includes
       |> List.filter_map (parse_include root)
     in
     let included_tops =
       included
       |> List.map (function Program(_ ,tops, _) -> tops)
       |> List.concat
     in
     Program(includes, included_tops@tops, tm)

let add_prelude = function
  | Program(includes, tops, tm) -> Program(default_includes@includes, tops, tm)

(* Main function for evaluation a function. Performs lexing, parsing
   and evaluation. Does not perform any type checking *)
let evalprog filename  =
  (* Make sure the filename is an absolute path, otherwise the duplicate file detection won't work *)
  let filename =
    if Filename.is_relative filename
    then Filename.concat (Sys.getcwd ()) filename
    else filename in
  if !utest then printf "%s: " filename;
  utest_fail_local := 0;
  begin try
    let parsed = parse_mcore_file filename in
    (parsed
     |> add_prelude
     |> merge_includes (Filename.dirname filename) [filename]
     |> Mlang.flatten
     |> Mlang.desugar_post_flatten
     |> debug_after_mlang
     |> Mexpr.symbolize builtin_name2sym
     |> debug_after_symbolize
     |> Mexpr.eval builtin_sym2term
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
  end; parsed_files := [];
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

(* Parse a string received by the REPL into an MCore AST *)
let parse_mcore_string str =
  Lexer.init (us "REPL") tablength;
  str |> Lexing.from_string
  |> Parser.main Lexer.main

(* Evaluate a term given existing environments.
   Returns updated environments along with evaluation result.
*)
let eval_with_envs (langs, nss, name2sym, sym2term) term =
  let new_langs, flattened = Mlang.flatten_with_env langs term in
  let new_nss, desugared = Mlang.desugar_post_flatten_with_nss nss flattened in
  let new_name2sym, symbolized = Mexpr.symbolize_toplevel name2sym desugared in
  let new_sym2term, result = Mexpr.eval_toplevel sym2term symbolized in
  ((new_langs, new_nss, new_name2sym, new_sym2term), result)

(* Read user input until the terminating sequence is encountered *)
let read_user_input () =
  let initial_prompt = ">> " in
  let followup_prompt = " | " in
  let rec read_new_line acc prompt =
    print_string prompt;
    let open BatString in
    let split_at str idx = (slice ~last:idx str, slice ~first:idx str) in
    let line = trim (read_line ()) in
    let first, last = split_at line (length line - 2) in
    match last with
    | ";;" -> sprintf "%s\n%s" acc first
    | _ -> read_new_line (sprintf "%s\n%s" acc line) followup_prompt
  in read_new_line "" initial_prompt

(* Run the MCore REPL *)
let runrepl _ =
  let repl_merge_includes = merge_includes (Sys.getcwd ()) [] in
  let rec read_eval_print envs =
    try
      let user_input = read_user_input () in
      let prog = user_input
                 |> parse_mcore_string
                 |> repl_merge_includes in
      let (new_envs, result) = eval_with_envs envs prog in
      uprint_endline (ustring_of_tm result);
      read_eval_print new_envs
    with e ->
      begin
        match e with
        | Lexer.Lex_error m -> uprint_endline (message2str m)
        | Parsing.Parse_error -> uprint_endline (message2str (Lexer.parse_error_message ()))
        | Error m -> uprint_endline (message2str m)
        | End_of_file -> exit 0
        | _ -> print_endline @@ Printexc.to_string e
      end;
      read_eval_print envs
  in
  let initial_term = Program([],[],TmConst(NoInfo,CInt(0)))
                     |> add_prelude
                     |> repl_merge_includes in
  let builtin_envs = (Record.empty, Mlang.USMap.empty, builtin_name2sym, builtin_sym2term) in
  let initial_envs, _ = eval_with_envs builtin_envs initial_term in
  print_endline "Welcome to the MCore REPL!";
  read_eval_print initial_envs

(* Run program *)
let runprog name lst =
    (* TODO prog_argv is never used anywhere *)
    prog_argv := lst;
    evalprog name

(* Print out main menu *)
let usage_msg = "Usage: miking [run|repl|test] <files>\n\nOptions:"

(* Main function. Checks arguments and reads file names *)
let main =

  (* A list of command line arguments *)
  let speclist = [

    (* First character in description string must be a space for alignment! *)
    "--debug-parse", Arg.Set(enable_debug_after_parse),
    " Enables output of parsing.";

    "--debug-mlang", Arg.Set(enable_debug_after_mlang),
    " Enables output of the mexpr program after mlang transformations.";

    "--debug-symbolize", Arg.Set(enable_debug_after_symbolize),
    " Enables output of the mexpr program after symbolize transformations.";

    "--debug-eval-tm", Arg.Set(enable_debug_eval_tm),
    " Enables output of terms in each eval step.";

    "--debug-eval-env", Arg.Set(enable_debug_eval_env),
    " Enables output of the environment in each eval step.";

    "--symbol", Arg.Set(enable_debug_symbol_print),
    " Enables output of symbols for variables. Affects all other debug printing.";

    "--full-pattern", Arg.Set(Patterns.pat_example_gives_complete_pattern),
    " Make the pattern analysis in mlang print full patterns instead of partial ones.";

  ] in

  (* Align the command line description list *)
  let speclist = Arg.align speclist in

  (* When non-option argument is encountered, simply save it to lst *)
  let lst = ref [] in
  let anon_fun arg = lst := arg :: !lst in

  (* Parse command line *)
  Arg.parse speclist anon_fun usage_msg;

  if List.length !lst = 0 then
    Arg.usage speclist usage_msg
  else
    match List.rev !lst with

    (* Run tests on one or more files *)
    | "test"::lst | "t"::lst -> testprog lst

    (* Start the MCore REPL *)
    | "repl"::lst -> runrepl lst

    (* Run one program with program arguments without typechecking *)
    | "run"::name::lst | name::lst -> runprog name lst

    (* Show the menu *)
    | _ -> Arg.usage speclist usage_msg
