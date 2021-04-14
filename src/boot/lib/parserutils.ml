open Ustring.Op
open Printf
open Ast
open Pprint
open Msg
module Option = BatOption

(* Tab length when calculating the info field *)
let tablength = 8

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

(* Standard lib default local path on unix (used by make install) *)
let stdlib_loc_unix =
  match Sys.getenv_opt "HOME" with
  | Some home ->
      home ^ "/.local/lib/mcore/stdlib"
  | None ->
      "@@@"

let stdlib_loc =
  match Sys.getenv_opt "MCORE_STDLIB" with
  | Some path ->
      path
  | None ->
      if Sys.os_type = "Unix" && Sys.file_exists stdlib_loc_unix then
        stdlib_loc_unix
      else "@@@"

let prog_argv : string list ref = ref []

(* Argv for the program that is executed *)

(* Debug printing after parse*)
let debug_after_parse t =
  if !enable_debug_after_parse then (
    printf "\n-- After parsing (only mexpr part) --\n" ;
    uprint_endline (ustring_of_program t) ;
    t )
  else t

(* Debug printing after symbolize transformation *)
let debug_after_symbolize t =
  if !enable_debug_after_symbolize then (
    printf "\n-- After symbolize --\n" ;
    uprint_endline (ustring_of_tm ~margin:80 t) ;
    t )
  else t

(* Debug mlang to mexpr transform *)
let debug_after_mlang t =
  if !enable_debug_after_mlang then (
    printf "\n-- After mlang --\n" ;
    uprint_endline (ustring_of_tm ~margin:80 t) ;
    t )
  else t

(* Keep track of which files have been parsed to avoid double includes *)
let parsed_files = ref []

(* Open a file and parse it into an MCore program *)
let local_parse_mcore_file filename =
  let fs1 = open_in filename in
  let p =
    Lexer.init (us filename) tablength ;
    fs1 |> Ustring.lexing_from_channel |> Parser.main Lexer.main
    |> debug_after_parse
  in
  close_in fs1 ;
  parsed_files := filename :: !parsed_files ;
  p

(* Parse and merge all files included from a program, given the
   path of the "root program". Raise an error if a loop is
   detected. *)
let rec merge_includes root visited = function
  | Program (includes, tops, tm) ->
      let rec parse_include root = function
        | Include (info, path) as inc ->
            let filename =
              Filename.concat root (Ustring.to_utf8 path)
              |> Utils.normalize_path
            in
            let file_stdloc =
              Filename.concat stdlib_loc (Ustring.to_utf8 path)
              |> Utils.normalize_path
            in
            if List.mem filename visited then
              raise_error info ("Cycle detected in included files: " ^ filename)
            else if List.mem filename !parsed_files then None
            else if
              Sys.file_exists filename
              && Sys.file_exists file_stdloc
              && file_stdloc <> filename
            then
              raise_error info
                ( "File exists both locally and in standard library: "
                ^ filename ) (* File already included *)
            else if Sys.file_exists filename then
              local_parse_mcore_file filename
              |> merge_includes
                   (Filename.dirname filename)
                   (filename :: visited)
              |> Option.some
            else if root != stdlib_loc && Sys.file_exists file_stdloc then
              parse_include stdlib_loc inc
            else raise_error info ("No such file: \"" ^ filename ^ "\"")
      in
      let included = includes |> List.filter_map (parse_include root) in
      let not_test = function TopUtest _ -> false | _ -> true in
      let included_tops =
        included
        |> List.map (function Program (_, tops, _) ->
               List.filter not_test tops )
        |> List.concat
      in
      Program (includes, included_tops @ tops, tm)

let parse_mexpr_string ustring =
  Lexer.init (us "internal") tablength ;
  ustring |> Ustring.lexing_from_ustring |> Parser.main_mexpr_tm Lexer.main

let parse_mcore_file filename =
  try
    parsed_files := [] ;
    let filename = Ustring.to_utf8 filename in
    local_parse_mcore_file filename
    |> merge_includes (Filename.dirname filename) [filename]
    |> Mlang.flatten |> Mlang.desugar_post_flatten
  with (Lexer.Lex_error _ | Error _ | Parsing.Parse_error) as e ->
    let error_string = Ustring.to_utf8 (error_to_ustring e) in
    fprintf stderr "%s\n" error_string ;
    exit 1
