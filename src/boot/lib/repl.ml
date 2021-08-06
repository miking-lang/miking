(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   repl.ml contains most of the MCore REPL functionality. It is built upon the
   bootstrap interpreter. Uses linenoise.
*)

open Ustring.Op
open Printf
open Ast
open Mlang
open Msg
open Pprint
open Intrinsics
open Parserutils
open Builtin
module Option = BatOption

let initial_prompt = ">> "

let followup_prompt = " | "

let no_line_edit = ref false

let history_file =
  if not !no_line_edit then
    try Sys.getenv "HOME" ^ "/.mcore_history"
    with Not_found ->
      failwith
        "$HOME is needed to save history, but it is unset. Either set it, or \
         disable line editing with --no-line-edit"
  else "@@@"

(* Try to parse a string received by the REPL into an MCore AST *)
let parse_mcore_string filename parse_fun str =
  let repl_tablength = 8 in
  Lexer.init (us filename) repl_tablength ;
  let lexbuf = Lexing.from_string str in
  try Ok (parse_fun Lexer.main lexbuf)
  with Parsing.Parse_error -> Error (Lexing.lexeme lexbuf)

let parse_prog_or_mexpr filename lines =
  match parse_mcore_string filename Parser.main lines with
  | Ok ast ->
      ast
  | Error _ -> (
    match parse_mcore_string filename Parser.main_mexpr lines with
    | Ok ast ->
        ast
    | Error _ ->
        raise Parsing.Parse_error )

let read_input prompt =
  if !no_line_edit then (print_string prompt ; read_line ())
  else
    match LNoise.linenoise prompt with
    | None ->
        raise End_of_file
    | Some str ->
        LNoise.history_add str |> ignore ;
        String.trim str

let save_history_and_exit () =
  if not !no_line_edit then
    LNoise.history_save ~filename:history_file |> ignore ;
  exit 0

let print_welcome_message () =
  print_endline "Welcome to the MCore REPL!" ;
  print_endline "Type :h for help or :q to quit."

let handle_command str =
  let help_message =
    {|  Commands available from the prompt:

   <statement>                 evaluate <statement>
   :{\n ..lines.. \n:}\n       multiline command
   :q                          exit the REPL
   :h                          display this message|}
  in
  match str with
  | ":q" ->
      save_history_and_exit ()
  | ":h" ->
      print_endline help_message ; true
  | _ ->
      false

(* Read and parse a toplevel or mexpr expression. Continues to read input
   until a valid expression is formed. Raises Parse_error if the expression
   cannot be extended to a valid expression *)
let rec read_until_complete is_mexpr input =
  let new_acc () = sprintf "%s\n%s" input (read_input followup_prompt) in
  let parse_fun = if is_mexpr then Parser.main_mexpr else Parser.main in
  match parse_mcore_string "REPL" parse_fun input with
  | Ok ast ->
      ast
  | Error "" ->
      read_until_complete is_mexpr (new_acc ())
  | Error _ ->
      if is_mexpr then raise Parsing.Parse_error
      else read_until_complete true input

(* Read and parse a multiline expression (:{\n ..lines.. \n:}).
   Returns None if the first line is not ":{" *)
let read_multiline first_line =
  let rec read_until_end acc =
    let line = read_input followup_prompt in
    match line with ":}" -> acc | _ -> read_until_end (line :: acc)
  in
  if first_line = ":{" then
    let lines =
      List.fold_right (fun x a -> sprintf "%s\n%s" a x) (read_until_end []) ""
    in
    Some (parse_prog_or_mexpr "REPL" lines)
  else None

(* Read input from the user and respond accordingly depending on if it is a
   command, the beginning of a multiline statement or a normal expression *)
let rec read_user_input () =
  let first_line = read_input initial_prompt in
  if handle_command first_line then read_user_input ()
  else
    Option.default_delayed
      (fun _ -> read_until_complete false first_line)
      (read_multiline first_line)

(* Evaluate a term given existing environments.
   Returns updated environments along with evaluation result.
*)
let eval_with_envs (langs, nss, name2sym, sym2term) term =
  let new_langs, flattened = flatten_with_env langs term in
  let new_nss, desugared = desugar_post_flatten_with_nss nss flattened in
  let new_name2sym, symbolized =
    Symbolize.symbolize_toplevel name2sym desugared
  in
  let new_sym2term, result = Mexpr.eval_toplevel sym2term symbolized in
  ((new_langs, new_nss, new_name2sym, new_sym2term), result)

(* Wrap the final mexpr in a lambda application to prevent scope leak *)
let wrap_mexpr (Program (inc, tops, tm)) =
  let lambda_wrapper =
    TmLam
      ( NoInfo
      , us "_"
      , Symb.Helpers.nosym
      , TyArrow (NoInfo, TyInt NoInfo, TyUnknown NoInfo)
      , tm )
  in
  let new_tm = TmApp (NoInfo, lambda_wrapper, TmConst (NoInfo, CInt 0)) in
  Program (inc, tops, new_tm)

let repl_merge_includes = merge_includes (Sys.getcwd ()) []

let repl_envs =
  ref (Record.empty, USMap.empty, builtin_name2sym, builtin_sym2term)

let initialize_envs () =
  let initial_envs, _ =
    Program ([], [], TmConst (NoInfo, CInt 0))
    |> repl_merge_includes |> eval_with_envs !repl_envs
  in
  repl_envs := initial_envs

let repl_eval_ast prog =
  let new_envs, result =
    prog |> repl_merge_includes |> wrap_mexpr |> eval_with_envs !repl_envs
  in
  repl_envs := new_envs ;
  result

let repl_format tm =
  match tm with
  | TmRecord (_, x) when Record.is_empty x ->
      None
  | TmConst (_, CPy obj) when Pyffi.is_none obj ->
      None
  | _ ->
      Some (ustring_of_tm tm)

(* Autocompletion *)
let begins_at str pos =
  let nonword_characters = Str.regexp "[][/\\\\(),={} \n\r\x0c\t]" in
  try Str.search_backward nonword_characters str (pos - 1) + 1
  with Not_found -> 0

let keywords = List.map fst Lexer.reserved_strings

module USSet = Set.Make (Ustring)

let keywords_and_identifiers () =
  let extract_name id =
    let sid =
      match id with
      | IdVar s ->
          s
      | IdCon s ->
          s
      | IdType s ->
          s
      | IdLabel s ->
          s
    in
    ustring_of_sid sid
  in
  let _, nss, name2sym, _ = !repl_envs in
  let names_without_langs =
    List.map
      (fun x -> x |> fst |> extract_name)
      (Symbolize.sym_env_to_assoc name2sym)
  in
  let replace_name name mangled_name names =
    names |> USSet.add name |> USSet.remove mangled_name
  in
  let process_lang lang ns names =
    names |> USSet.add lang
    |> USMap.fold replace_name ns.constructors
    |> USMap.fold replace_name ns.normals
  in
  names_without_langs |> USSet.of_list
  |> USMap.fold process_lang nss
  |> USSet.to_seq |> List.of_seq |> List.map Ustring.to_utf8 |> ( @ ) keywords

let get_matches s =
  s |> BatPervasives.flip BatString.starts_with |> List.filter

let get_completions str pos =
  let start_pos = begins_at str pos in
  let word_to_complete = BatString.slice ~first:start_pos ~last:pos str in
  (start_pos, get_matches word_to_complete (keywords_and_identifiers ()))

let completion_callback line_so_far ln_completions =
  let start_pos, raw_completions =
    get_completions line_so_far (String.length line_so_far)
  in
  let line_beginning = String.sub line_so_far 0 start_pos in
  let completions = List.map (sprintf "%s%s" line_beginning) raw_completions in
  List.iter (LNoise.add_completion ln_completions) completions

let init_linenoise () =
  if not !no_line_edit then (
    LNoise.set_completion_callback completion_callback ;
    LNoise.history_load ~filename:history_file |> ignore )

(* Run the MCore REPL *)
let start_repl () =
  let repl_print tm =
    match repl_format tm with
    | None ->
        flush stdout
    | Some str ->
        uprint_endline str
  in
  let rec read_eval_print () =
    try
      read_user_input () |> repl_eval_ast |> repl_print ;
      read_eval_print ()
    with e ->
      ( match e with
      | Sys.Break ->
          ()
      | End_of_file ->
          save_history_and_exit ()
      | _ ->
          uprint_endline @@ error_to_ustring e ) ;
      read_eval_print ()
  in
  print_welcome_message () ;
  init_linenoise () ;
  initialize_envs () ;
  read_eval_print ()
