open Printf

let menu () =
  printf
    "Usage: run <benchmark-name-without-postfix-name> <iteration> [excludes]\n\n" ;
  printf "Example: run factorial 1000\n\n" ;
  printf "To exclude certain tests, add excluded numbers. For instance\n" ;
  printf "command 'run factorial 1000 24' excludes the Miking interpreter\n" ;
  printf "and OCaml byte code tests (test numbers 2 and 4).\n" ;
  exit 1

let measure excludes number str pre_cmd cmd post_cmd =
  (* printf "\n\npre_cmd: %s\ncmd: %s\npost_cmd: %s\n" pre_cmd cmd post_cmd ; *)
  if String.contains excludes (string_of_int number).[0] then ()
  else (
    printf "%d. %s " number str ;
    flush stdout ;
    let to_null = " 2>&1 >/dev/null" in
    let _ = Sys.command (pre_cmd ^ to_null) in
    let run () =
      let l1 = Unix.gettimeofday () in
      let _ = Sys.command (cmd ^ to_null) in
      let l2 = Unix.gettimeofday () in
      printf "%10fs" (l2 -. l1) ;
      flush stdout
    in
    run () ;
    run () ;
    let _ = Sys.command (post_cmd ^ to_null) in
    printf "\n" ; flush stdout )

let main =
  let len = Array.length Sys.argv in
  let name, iterations =
    if len >= 3 then (Sys.argv.(1), Sys.argv.(2)) else menu ()
  in
  let excludes = if len >= 4 then Sys.argv.(3) else "" in
  let name_mc = name ^ ".mc" in
  let _ = Sys.command "rm -rf _build" in
  if Sys.file_exists name_mc then (
    measure excludes 1 "Boot interpreter:  " ""
      ("boot eval " ^ name_mc ^ " -- " ^ iterations)
      "" ;
    measure excludes 2 "Miking interpreter:" ""
      ("mi eval " ^ name_mc ^ " -- " ^ iterations)
      "" ;
    measure excludes 3 "Miking compiler:   " ("mi compile " ^ name_mc)
      ("./" ^ name ^ " " ^ iterations)
      ("rm -f " ^ name) ;
    if Sys.file_exists (name ^ ".ml") then (
      measure excludes 4 "OCaml byte code    "
        ("ocamlbuild " ^ name ^ ".byte")
        ("ocamlrun " ^ name ^ ".byte" ^ " " ^ iterations)
        ("rm -f " ^ name ^ ".byte") ;
      measure excludes 5 "OCaml native:      "
        ("ocamlbuild " ^ name ^ ".native")
        ("./" ^ name ^ ".native" ^ " " ^ iterations)
        ("rm -f " ^ name ^ ".native") )
    else () )
  else printf "ERROR: Cannot find file %s.mc\n" name
