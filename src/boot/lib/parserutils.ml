open Ustring.Op
open Printf
open Ast
open Pprint
open Msg
open Symbutils

(* Tab length when calculating the info field *)
let tablength = 8

let error_to_error_message = function
  | Lexer.Lex_error m | Error m ->
      Some m
  | Parser.Error ->
      Some (Lexer.parse_error_message ())
  | _ ->
      None

let error_to_ustring e =
  match error_to_error_message e with
  | Some m ->
      message2str m
  | None ->
      us (Printexc.to_string e)

module ExtIdMap = Map.Make (Ustring)

let raise_parse_error_on_non_unique_external_id t =
  let rec recur acc = function
    | TmExt (fi, id, _, _, _, t) -> (
        ExtIdMap.find_opt id acc
        |> function
        | Some fi' ->
            raise
              (Error
                 ( PARSE_ERROR
                 , ERROR
                 , fi
                 , [id; us "already defined at"; info2str fi'] ) )
        | None ->
            recur (ExtIdMap.add id fi acc) t )
    | t ->
        sfold_tm_tm recur acc t
  in
  let _ = recur ExtIdMap.empty t in
  t

(* NOTE(oerikss, 2021-04-22) this function should be applied on a symbolized
 * term *)
let raise_parse_error_on_partially_applied_external t =
  let rec recur ((symb_map, app_depth, fi) as acc) = function
    | TmExt (_, _, s, _, ty, t) ->
        let symb_map' = SymbMap.add s (ty_arity ty) symb_map in
        recur (symb_map', app_depth, fi) t
    | TmApp (fi, t1, t2) ->
        let _ = recur (symb_map, app_depth + 1, fi) t1 in
        recur (symb_map, 0, NoInfo) t2
    | TmVar (_, id, s, _, _) -> (
        SymbMap.find_opt s symb_map
        |> function
        | Some arity ->
            if arity > app_depth then
              raise
                (Error (PARSE_ERROR, ERROR, fi, [id; us "partially applied"]))
            else acc
        | None ->
            acc )
    | t ->
        sfold_tm_tm recur (symb_map, 0, NoInfo) t
  in
  let _ = recur (SymbMap.empty, 0, NoInfo) t in
  t

(* NOTE(oerikss, 2021-10-21) this function should be applied on a symbolized
 * term *)
let prune_external_utests ?(enable = true) ?(warn = true)
    ?(externals_exclude = []) t =
  let module Set = Set.Make (Ustring) in
  let externals_exclude = Set.of_list externals_exclude in
  (* The accumulator [(sm, ntests, hasref)] contains, [sm], a map from symbols
     that references an external to their identifier, [ntests] the number of
     removed utests, and [hasref] which is a Boolean indicating if a sub
     expression contains references to an external *)
  let rec recur (sm, ntests, hasref) = function
    | TmVar (_, _, s, _, _) as t ->
        ((sm, ntests, SymbMap.mem s sm || hasref), t)
    | TmExt (fi, x, s, ty, e, t) ->
        let sm, hasref' =
          if Set.mem x externals_exclude then (sm, false)
          else (SymbMap.add s x sm, true)
        in
        recur (sm, ntests, false) t
        |> fun ((sm, ntests, hasref''), t') ->
        ( (sm, ntests, hasref || hasref' || hasref'')
        , TmExt (fi, x, s, ty, e, t') )
    | TmLet (fi, x, s, ty, t1, t2) ->
        recur (sm, ntests, false) t1
        |> fun ((sm, ntests, hasref'), t1') ->
        recur ((if hasref' then SymbMap.add s x sm else sm), ntests, false) t2
        |> fun ((sm, ntests, hasref''), t2') ->
        ( (sm, ntests, hasref || hasref' || hasref'')
        , TmLet (fi, x, s, ty, t1', t2') )
    | TmRecLets (fi, lst, t) ->
        List.fold_left_map
          (fun (sm, ntests, hasref) (fi, x, s, ty, t) ->
            recur (sm, ntests, false) t
            |> fun ((sm, ntests, hasref'), t') ->
            ( ( (if hasref' then SymbMap.add s x sm else sm)
              , ntests
              , hasref || hasref' )
            , (fi, x, s, ty, t') ) )
          (sm, ntests, false) lst
        |> fun ((sm, ntests, hasref'), lst') ->
        recur (sm, ntests, false) t
        |> fun ((sm, ntests, hasref''), t') ->
        ((sm, ntests, hasref || hasref' || hasref''), TmRecLets (fi, lst', t'))
    | TmUtest (fi, t1, t2, t3, t4, t5) ->
        recur (sm, ntests, false) t1
        |> fun ((sm, ntests, hasref'), t1') ->
        recur (sm, ntests, hasref') t2
        |> fun ((sm, ntests, hasref'), t2') ->
        ( match t3 with
        | Some t3' ->
            let (sm, ntests, hasref'), t3' = recur (sm, ntests, hasref') t3' in
            ((sm, ntests, hasref'), Some t3')
        | None ->
            ((sm, ntests, hasref'), t3) )
        |> fun ((sm, ntests, hasref'), t3') ->
        ( match t4 with
        | Some t4' ->
            let (sm, ntests, hasref'), t4' = recur (sm, ntests, hasref') t4' in
            ((sm, ntests, hasref'), Some t4')
        | None ->
            ((sm, ntests, hasref'), t4) )
        |> fun ((sm, ntests, hasref'), t4') ->
        recur (sm, ntests, false) t5
        |> fun ((sm, ntests, hasref''), t5') ->
        if hasref' then ((sm, succ ntests, hasref || hasref''), t5')
        else
          ( (sm, ntests, hasref || hasref'')
          , TmUtest (fi, t1', t2', t3', t4', t5') )
    | t ->
        smap_accum_left_tm_tm recur (sm, ntests, hasref) t
  in
  if enable then (
    let (_, ntests, _), t' = recur (SymbMap.empty, 0, false) t in
    if ntests > 0 && warn then
      Printf.printf
        "\n\
         WARNING: Removed %d utests referencing external dependent identifiers.\n"
        ntests
    else () ;
    t' )
  else t

let prune_external_utests_boot t =
  prune_external_utests
    ~enable:(!utest && not !disable_prune_external_utests)
    ~warn:(not !disable_prune_external_utests_warning)
    t

let rec remove_all_utests = function
  | TmUtest (_, _, _, _, _, t) ->
      remove_all_utests t
  | t ->
      smap_tm_tm remove_all_utests t

(* Current working directory standard library path *)
let stdlib_cwd = Filename.concat (Sys.getcwd ()) "stdlib"

(* Standard lib default local path on unix (used by make install) *)
let stdlib_loc_unix =
  match Sys.getenv_opt "HOME" with
  | Some home ->
      home ^ "/.local/lib/mcore/stdlib"
  | None ->
      stdlib_cwd

module NamespaceMap = Map.Make (String)

let namespaces : string NamespaceMap.t =
  let process_binding str =
    if Str.string_match (Str.regexp {|\([^=]+\)=\(.+\)|}) str 0 then
      Some (Str.matched_group 1 str, Str.matched_group 2 str)
    else
      let msg =
        error_message NoInfo WARNING
          ( "Invalid element of MCORE_LIBS: \"" ^ str
          ^ "\", expected a key=value pair" )
      in
      eprintf "%s\n" (message2str msg |> Ustring.to_utf8) ;
      None
  in
  let env_bindings =
    match Sys.getenv_opt "MCORE_LIBS" with
    | Some path ->
        path
        |> Str.split (Str.regexp ":")
        |> List.to_seq
        |> Seq.filter_map process_binding
    | None ->
        Seq.empty
  in
  NamespaceMap.add_seq env_bindings NamespaceMap.empty

let (stdlib_loc : string), (library_locs : string NamespaceMap.t) =
  match NamespaceMap.find_opt "stdlib" namespaces with
  | Some stdlib ->
      (stdlib, namespaces)
  | None ->
      let stdlib =
        if Sys.os_type = "Unix" && Sys.file_exists stdlib_loc_unix then
          stdlib_loc_unix
        else stdlib_cwd
      in
      (stdlib, NamespaceMap.add "stdlib" stdlib namespaces)

let process_include_path : info -> string -> string -> string =
 fun info root path ->
  let check_exists file =
    if Sys.file_exists file then file
    else raise_error info ("No such file: \"" ^ file ^ "\"")
  in
  let path_from_namespace namespace filename =
    match NamespaceMap.find_opt namespace library_locs with
    | Some root' ->
        let namespace_path =
          Filename.concat root' filename |> Utils.normalize_path
        in
        check_exists namespace_path
    | None ->
        raise_error info ("Unknown file namespace: \"" ^ namespace ^ "\"")
  in
  let path_from_implicit local_path stdlib_path =
    if local_path = stdlib_path then check_exists local_path
    else
      match (Sys.file_exists local_path, Sys.file_exists stdlib_path) with
      | true, false ->
          local_path
      | false, true ->
          stdlib_path
      | true, true ->
          raise_error info
            ("File exists both locally and in standard library: " ^ path)
      | false, false ->
          raise_error info ("No such file: \"" ^ path ^ "\"")
  in
  if Str.string_match (Str.regexp {|\(.+\)::\(.+\)|}) path 0 then
    path_from_namespace (Str.matched_group 1 path) (Str.matched_group 2 path)
  else
    let local_path = Filename.concat root path |> Utils.normalize_path in
    if not (Filename.is_implicit path) then check_exists local_path
    else
      path_from_implicit local_path
        (Filename.concat stdlib_loc path |> Utils.normalize_path)

let prog_argv : string list ref = ref []

(* Argv for the program that is executed *)

(* Debug printing after parse*)
let debug_after_parse t =
  if !enable_debug_after_parse then (
    printf "\n-- After parsing (only mexpr part) --\n" ;
    uprint_endline (ustring_of_program t) ;
    print_endline "" ;
    t )
  else t

(* Debug printing after symbolize transformation *)
let debug_after_symbolize t =
  if !enable_debug_after_symbolize then (
    printf "\n-- After symbolize --\n" ;
    uprint_endline (ustring_of_tm ~margin:80 t) ;
    t )
  else t

(* Debug printing after external dependent utest removal *)
let debug_after_pruning_external_utests t =
  if !enable_debug_after_prune_external_utests then (
    printf "\n-- After external utest pruning  --\n" ;
    uprint_endline (ustring_of_tm ~margin:80 t) ;
    t )
  else t

(* Debug printing after dead code elimination *)
let debug_after_dead_code_elimination t =
  if !enable_debug_after_dead_code_elimination then (
    printf "\n-- After dead code elimination --\n" ;
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
    let lexbuf = Ustring.lexing_from_channel fs1 in
    try Parser.main Lexer.main lexbuf |> debug_after_parse
    with Parser.Error -> raise_error !Lexer.last_info "Parse error"
  in
  close_in fs1 ;
  parsed_files := filename :: !parsed_files ;
  p

(* Parse and merge all files included from a program, given the
   path of the "root program". Raise an error if a loop is
   detected. *)
let rec merge_includes root visited = function
  | Program (includes, tops, tm) ->
      let parse_include root = function
        | Include (info, path) ->
            let path = Ustring.to_utf8 path in
            let filename = process_include_path info root path in
            if List.mem filename visited then
              raise_error info ("Cycle detected in included files: " ^ filename)
            else if List.mem filename !parsed_files then None
            else
              local_parse_mcore_file filename
              |> merge_includes
                   (Filename.dirname filename)
                   (filename :: visited)
              |> Option.some
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

let parse_mlang_string ustring =
  Lexer.init (us "internal") tablength ;
  ustring |> Ustring.lexing_from_ustring |> Parser.main Lexer.main

(* Parse an MCore file and merge includes. Expects a normalized filename. *)
let parse_mcore_file filename =
  parsed_files := [] ;
  local_parse_mcore_file filename
  |> merge_includes (Filename.dirname filename) [filename]
