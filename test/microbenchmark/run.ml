open Printf

let usage_msg =
  "run [-i <iterations>] [-e <excludes>] [-t <timeout>] <BENCHMARK> \
   [BENCHMARK] ...\n\n\
  \ where BENCHMARK is the benchmark filename without file suffix."

let iterations = ref 100

let excludes = ref None

let timeout = ref None

let benchmarks = ref []

let speclist =
  [ ( "-i"
    , Arg.Set_int iterations
    , "Numer of iterations to run for each benchmark (default "
      ^ string_of_int !iterations ^ ")" )
  ; ( "-e"
    , Arg.String (fun e -> excludes := Some e)
    , "Tests to excludes,\n\
      \ e.g. -e 25 exlcudes tests 2 and 5 (the Miking interpreter and OCaml \
       byte code tests)" )
  ; ( "-t"
    , Arg.Int (fun t -> timeout := Some t)
    , "Number of iterations to run for each benchmark" ) ]

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
  Arg.parse speclist
    (fun benchmark -> benchmarks := benchmark :: !benchmarks)
    usage_msg ;
  match !benchmarks with
  | [] ->
      Arg.usage speclist usage_msg
  | _ ->
      (let excludes = Option.value ~default:"" !excludes in
       let iterations = string_of_int !iterations in
       let timeout = !timeout in
       let _ = Sys.command "rm -rf _build" in
       List.iter (fun name ->
           let name_mc = name ^ ".mc" in
           if Sys.file_exists name_mc then (
             measure excludes 1 "Boot interpreter:     " ""
               ("boot eval " ^ name_mc ^ " -- " ^ iterations)
               "" timeout ;
             measure excludes 2 "Miking interpreter:   " ""
               ("mi eval " ^ name_mc ^ " -- " ^ iterations)
               "" timeout ;
             measure excludes 3 "Miking compiler:      "
               ("mi compile " ^ name_mc)
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
                   ( "ocamlrun _build/default/" ^ name ^ ".bc" ^ " "
                   ^ iterations )
                   "rm -rf _build" timeout ;
                 measure excludes 6 "OCaml native:         "
                   ("dune build --root ." ^ " " ^ name ^ ".exe")
                   ("./_build/default/" ^ name ^ ".exe" ^ " " ^ iterations)
                   "rm -rf _build && rm dune*" )
                 timeout
             else () )
           else printf "ERROR: Cannot find file %s.mc\n" name ) )
        !benchmarks
