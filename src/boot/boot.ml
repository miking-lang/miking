
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

(* TODO: Temporary fix for hackinar installation issues *)
module Option = struct
  let some x = Some x
  let is_some = function
    | Some _ -> true
    | None -> false
  let get = function
    | Some x -> x
    | None -> failwith "Not Some"
end

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

(* Keep track of which files have been parsed to avoid double includes *)
let parsed_files = ref []

(* Open a file and parse it into an MCore program *)
let parse_mcore_file filename =
  let fs1 = open_in filename in
  let tablength = 8 in
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
          let filename = Filename.concat root (Ustring.to_utf8 path) in
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
  if !utest then printf "%s: " filename;
  utest_fail_local := 0;
  begin try
    let parsed = parse_mcore_file filename in
    (parsed
     |> add_prelude
     |> merge_includes (Filename.dirname filename) [filename]
     |> Mlang.flatten
     |> Mlang.desugar_post_flatten
     |> Mexpr.debruijn (builtin |> List.split |> fst |> (List.map (fun x-> VarTm(us x))))
     |> debug_after_debruijn
     |> Mexpr.eval (builtin |> List.split |> snd |> List.map (fun x -> TmConst(NoInfo,x)))
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
