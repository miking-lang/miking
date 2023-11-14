(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   boot.ml is the main entry point for first stage of the
   bootstrapped Miking compiler. The bootstapper is interpreted and
   implemented in OCaml. Note that the Miking bootstrapper
   only implements a subset of the Ragnar language.
*)

open Printf
open Boot.Ast
open Boot.Builtin
open Boot.Eval
open Boot.Repl

(* Add a slash at the end "\\" or "/" if not already available *)
let add_slash s =
  if String.length s = 0 then Filename.dir_sep else Filename.concat s ""

(* Expand a list of files and folders into a list of file names *)
let files_of_folders lst =
  List.fold_left
    (fun a v ->
      if Sys.is_directory v then
        ( Sys.readdir v |> Array.to_list
        |> List.filter (fun x -> not (String.length x >= 1 && x.[0] = '.'))
        |> List.map (fun x -> add_slash v ^ x)
        |> List.filter (fun x -> not (Sys.is_directory x))
        |> List.filter (fun x ->
               not (String.contains x '#' || String.contains x '~') ) )
        @ a
      else v :: a )
    [] lst

(* Iterate over all potential test files and run tests *)
let testprog lst =
  (* Select the lexer and parser, depending on the DSL*)
  let eprog name = evalprog name in
  (* Evaluate each of the programs in turn *)
  List.iter eprog (files_of_folders lst) ;
  (* Print out unit test results, if applicable *)
  if !utest_fail = 0 then
    printf "Unit testing SUCCESSFUL after executing %d tests.\n\n" !utest_ok
  else (
    printf "ERROR! %d successful tests and %d failed tests.\n\n" !utest_ok
      !utest_fail ;
    exit 1 )

(* Run the REPL *)
let runrepl _ = start_repl ()

(* Print out main menu *)
let usage_msg = "Usage: boot [eval|repl] <files>\n\nOptions:"

(* Main function. Checks arguments and reads file names *)
let main =
  (* A list of command line arguments *)
  let speclist =
    [ (* First character in description string must be a space for alignment! *)
      ("--test", Arg.Set utest, " Run unit tests.")
    ; ( "--debug-parse"
      , Arg.Set enable_debug_after_parse
      , " Enables output of parsing." )
    ; ( "--debug-mlang"
      , Arg.Set enable_debug_after_mlang
      , " Enables output of the mexpr program after mlang transformations." )
    ; ( "--debug-symbolize"
      , Arg.Set enable_debug_after_symbolize
      , " Enables output of the mexpr program after symbolize transformations."
      )
    ; ( "--debug-utest-pruning"
      , Arg.Set enable_debug_after_prune_external_utests
      , " Enables output of the mexpr program after external utests pruning."
      )
    ; ( "--debug-dead-code-elim"
      , Arg.Set enable_debug_after_dead_code_elimination
      , " Enables output of the mexpr program after dead code elimination." )
    ; ( "--debug-dead-code-info"
      , Arg.Set enable_debug_dead_code_info
      , " Enables output of dead code elimination info." )
    ; ( "--debug-eval-tm"
      , Arg.Set enable_debug_eval_tm
      , " Enables output of terms in each eval step." )
    ; ( "--debug-eval-env"
      , Arg.Set enable_debug_eval_env
      , " Enables output of the environment in each eval step." )
    ; ( "--debug-con-shapes"
      , Arg.Set enable_debug_con_shape
      , " Enables printing of the shape of values given to constructors, to \
         stderr." )
    ; ( "--debug-stack-trace"
      , Arg.Set enable_debug_stack_trace
      , " Enables printing of a stack trace when errors occur." )
    ; ( "--debug-profile"
      , Arg.Set enable_debug_profiling
      , " Enables printing of number of calls to and cumulative runtime of \
         closures." )
    ; ( "--symbol"
      , Arg.Set enable_debug_symbol_print
      , " Enables output of symbols for variables. Affects all other debug \
         printing." )
    ; ( "--full-pattern"
      , Arg.Set Boot.Patterns.pat_example_gives_complete_pattern
      , " Make the pattern analysis in mlang print full patterns instead of \
         partial ones." )
    ; ( "--disable-prune-utests"
      , Arg.Set disable_prune_external_utests
      , " Disables pruning of utests with missing external dependencies." )
    ; ( "--disable-prune-warning"
      , Arg.Set disable_prune_external_utests_warning
      , " Disable warning when pruning utests with missing external \
         dependencies" )
    ; ( "--disable-dead-code-elim"
      , Arg.Set disable_dead_code_elimination
      , " Disables dead code elimination." )
    ; ( "--no-line-edit"
      , Arg.Set Boot.Repl.no_line_edit
      , " Disable line editing funcionality in the REPL." ) ]
  in
  (* Align the command line description list *)
  let speclist = Arg.align speclist in
  (* When non-option argument is encountered, simply save it to lst *)
  let lst = ref [] in
  let anon_fun arg = lst := arg :: !lst in
  (* Parse command line *)
  ( try Arg.parse_argv argv_boot speclist anon_fun usage_msg
    with Arg.Bad m | Arg.Help m -> print_endline m ; exit 0 ) ;
  if List.length !lst = 0 then Arg.usage speclist usage_msg
  else
    match List.rev !lst with
    (* Start the MCore REPL *)
    | "repl" :: lst ->
        runrepl lst
    (* Eval one program with program arguments without typechecking *)
    | "eval" :: (name :: _ as lst) ->
        if !utest then testprog lst else evalprog name
    (* Show the menu *)
    | _ ->
        Arg.usage speclist usage_msg
