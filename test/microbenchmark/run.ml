open Printf

let menu () =
  printf
    "Usage: run <benchmark-name-without-postfix-name> <iteration> [excludes] \
     [timeout]\n\n" ;
  printf "Example: run factorial 1000\n\n" ;
  printf "To exclude certain tests, add excluded numbers. For instance\n" ;
  printf "command 'run factorial 1000 25' excludes the Miking interpreter\n" ;
  printf "and OCaml byte code tests (test numbers 2 and 5).\n" ;
  printf "The argument timeout give a timeout in seconds.\n" ;
  exit 1

let measure excludes number str pre_cmd cmd post_cmd timeout =
  (* printf "\n\npre_cmd: %s\ncmd: %s\npost_cmd: %s\n" pre_cmd cmd post_cmd ; *)
  if String.contains excludes (string_of_int number).[0] then ()
  else (
    printf "%d. %s " number str ;
    let to_null = " 2>&1 >/dev/null" in
    let _ = Sys.command (pre_cmd ^ to_null) in
    let run () =
      let command = cmd ^ to_null in
      let command =
        match timeout with
        | Some timeout ->
            "timeout " ^ string_of_int timeout ^ " " ^ command
        | None ->
            command
      in
      let l1 = Unix.gettimeofday () in
      let rc = Sys.command command in
      let l2 = Unix.gettimeofday () in
      printf "%10f%s" (l2 -. l1)
        (if rc = 124 && Option.is_some timeout then "s (timeout)" else "s") ;
      flush stdout
    in
    run () ;
    run () ;
    let _ = Sys.command (post_cmd ^ to_null) in
    printf "\n" ; flush stdout )

let generate_dune name =
  let oc = open_out "dune" in
  Printf.fprintf oc
    "(env\n\
    \       (dev\n\
    \          (flags (:standard -w -a))\n\
    \          (ocamlc_flags (-without-runtime))))\n\n\
    \      (executable\n\
    \         (name %s)\n\
    \         (libraries str owl)\n\
    \         (modes byte exe))" name ;
  close_out oc

let generate_dune_project () =
  let oc = open_out "dune-project" in
  Printf.fprintf oc "(lang dune 2.0)" ;
  close_out oc

let main =
  let len = Array.length Sys.argv in
  let name, iterations =
    if len >= 3 then (Sys.argv.(1), Sys.argv.(2)) else menu ()
  in
  let excludes = if len >= 4 then Sys.argv.(3) else "" in
  let timeout = if len >= 5 then Some (int_of_string Sys.argv.(4)) else None in
  let name_mc = name ^ ".mc" in
  let _ = Sys.command "rm -rf _build" in
  if Sys.file_exists name_mc then (
    measure excludes 1 "Boot interpreter:     " ""
      ("boot eval " ^ name_mc ^ " -- " ^ iterations)
      "" timeout ;
    measure excludes 2 "Miking interpreter:   " ""
      ("mi eval " ^ name_mc ^ " -- " ^ iterations)
      "" timeout ;
    measure excludes 3 "Miking compiler:      " ("mi compile " ^ name_mc)
      ("./" ^ name ^ " " ^ iterations)
      ("rm -f " ^ name) timeout ;
    measure excludes 4 "Miking compiler (opt):"
      ("mi compile --enable-constant-fold " ^ name_mc)
      ("./" ^ name ^ " " ^ iterations)
      ("rm -f " ^ name) timeout ;
    if Sys.file_exists (name ^ ".ml") then
      ( generate_dune name ;
        generate_dune_project () ;
        measure excludes 5 "Ocaml byte code       "
          ("dune build --root ." ^ " " ^ name ^ ".bc")
          ("ocamlrun _build/default/" ^ name ^ ".bc" ^ " " ^ iterations)
          "rm -rf _build" timeout ;
        measure excludes 6 "OCaml native:         "
          ("dune build --root ." ^ " " ^ name ^ ".exe")
          ("./_build/default/" ^ name ^ ".exe" ^ " " ^ iterations)
          "rm -rf _build && rm dune*" )
        timeout
    else () )
  else printf "ERROR: Cannot find file %s.mc\n" name
