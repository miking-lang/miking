
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   repl.ml contains most of the MCore REPL functionality. It is built upon the
   bootstrap interpreter. Uses linenoise.
*)


open Ustring.Op
open Printf
open Eval
open Mexpr
open Ast
open Msg
open Pprint

let initial_prompt = ">> "
let followup_prompt = " | "

let no_line_edit = ref false

module Option = BatOption


(* Try to parse a string received by the REPL into an MCore AST *)
let parse_mcore_string parse_fun str =
  let repl_tablength = 8 in
  Lexer.init (us"REPL") repl_tablength;
  let lexbuf = Lexing.from_string str in
  try Ok (parse_fun Lexer.main lexbuf)
  with Parsing.Parse_error -> Error (Lexing.lexeme lexbuf)

let parse_prog_or_mexpr lines =
  match parse_mcore_string Parser.main lines with
  | Ok ast -> ast
  | Error _ ->
    match parse_mcore_string Parser.main_mexpr lines with
    | Ok ast -> ast
    | Error _ -> raise Parsing.Parse_error

let read_input prompt =
  if !no_line_edit then
    (print_string prompt; read_line ())
  else
    match LNoise.linenoise prompt with
    | None -> raise End_of_file
    | Some str ->
      LNoise.history_add str |> ignore;
      String.trim str

let print_welcome_message () =
  print_endline "Welcome to the MCore REPL!";
  print_endline "Type :h for help or :q to quit."

let handle_command str =
  let help_message =
{|  Commands available from the prompt:

   <statement>                 evaluate <statement>
   :{\n ..lines.. \n:}\n       multiline command
   :q                          exit the REPL
   :h                          display this message|} in
  match str with
  | ":q" -> exit 0
  | ":h" -> print_endline help_message; true
  | _ -> false

(* Read and parse a toplevel or mexpr expression. Continues to read input
   until a valid expression is formed. Raises Parse_error if the expression
   cannot be extended to a valid expression *)
let rec read_until_complete is_mexpr input =
  let new_acc () = sprintf "%s\n%s" input (read_input followup_prompt) in
  let parse_fun = if is_mexpr then Parser.main_mexpr else Parser.main in
  match parse_mcore_string parse_fun input with
  | Ok ast -> ast
  | Error "" -> read_until_complete is_mexpr (new_acc ())
  | Error _ ->
    if is_mexpr then
      raise Parsing.Parse_error
    else
      read_until_complete true input

(* Read and parse a multiline expression (:{\n ..lines.. \n:}).
   Returns None if the first line is not ":{" *)
let read_multiline first_line =
  let rec read_until_end acc =
    let line = read_input followup_prompt in
    match line with
    | ":}" -> acc
    | _ -> read_until_end (line :: acc)
  in
  if first_line = ":{" then
    let lines = List.fold_right (fun x a -> sprintf "%s\n%s" a x)
                                (read_until_end []) "" in
    Some (parse_prog_or_mexpr lines)
  else
    None

(* Read input from the user and respond accordingly depending on if it is a
   command, the beginning of a multiline statement or a normal expression *)
let rec read_user_input () =
  let first_line = read_input initial_prompt in
  if handle_command first_line then
    read_user_input ()
  else
    Option.default_delayed (fun _ -> read_until_complete false first_line)
                           (read_multiline first_line)

(* Evaluate a term given existing environments.
   Returns updated environments along with evaluation result.
*)
let eval_with_envs (langs, nss, name2sym, sym2term) term =
  let new_langs, flattened = Mlang.flatten_with_env langs term in
  let new_nss, desugared = Mlang.desugar_post_flatten_with_nss nss flattened in
  let new_name2sym, symbolized = Mexpr.symbolize_toplevel name2sym desugared in
  let new_sym2term, result = Mexpr.eval_toplevel sym2term symbolized in
  ((new_langs, new_nss, new_name2sym, new_sym2term), result)

(* Wrap the final mexpr in a lambda application to prevent scope leak *)
let wrap_mexpr (Program(inc, tops, tm)) =
  let lambda_wrapper = TmLam(NoInfo, us"_", nosym, TyArrow(TyInt,TyDyn), tm) in
  let new_tm = TmApp(NoInfo, lambda_wrapper, TmConst(NoInfo, CInt(0))) in
  Program(inc, tops, new_tm)

let repl_merge_includes = merge_includes (Sys.getcwd ()) []

let repl_envs = ref (Record.empty, Mlang.USMap.empty, builtin_name2sym, builtin_sym2term)

let initialize_envs () =
  let initial_envs, _ = Program([],[],TmConst(NoInfo,CInt(0)))
                        |> add_prelude
                        |> repl_merge_includes
                        |> eval_with_envs !repl_envs in
  repl_envs := initial_envs

let repl_eval_ast prog =
  let new_envs, result = prog
    |> repl_merge_includes
    |> wrap_mexpr
    |> eval_with_envs !repl_envs in
  repl_envs := new_envs;
  result

(* Run the MCore REPL *)
let start_repl () =
  let rec read_eval_print () =
    try
      let (Program(_,_,tm)) as ast = read_user_input () in
      let result = repl_eval_ast ast in
      begin
        if tm = tmUnit then
          flush stdout
        else
          uprint_endline (ustring_of_tm result)
      end;
      read_eval_print ()
    with e ->
      begin
        match e with
        | Lexer.Lex_error m -> uprint_endline (message2str m)
        | Parsing.Parse_error -> uprint_endline (message2str (Lexer.parse_error_message ()))
        | Error m -> uprint_endline (message2str m)
        | Sys.Break -> ()
        | End_of_file -> exit 0
        | _ -> print_endline @@ Printexc.to_string e
      end;
      read_eval_print ()
  in
  print_welcome_message ();
  initialize_envs ();
  read_eval_print ()
