
open Printf

let menu() =
  printf "Usage: run <benchmark-name-without-postfix-name> <iteration> [excludes]\n\n";
  printf "Example: run factorial 1000\n\n";
  exit 1


let measure str pre_cmd cmd post_cmd =
  printf "%s: " str; flush stdout;
  let to_null = " 2>&1 >/dev/null" in
  let _ = Sys.command (pre_cmd ^ to_null) in
  let l1 = Unix.gettimeofday() in
  let _ = Sys.command (cmd ^ to_null) in
  let l2 = Unix.gettimeofday() in
  let _ = Sys.command (post_cmd ^ to_null) in
  printf "%fs\n" (l2 -. l1); flush stdout

let main =
  let len = Array.length Sys.argv  in
  let (name, iterations) = if len >= 3 then (Array.get Sys.argv 1, Array.get Sys.argv 2) else menu() in
  let name_mc = name ^ ".mc" in
  if Sys.file_exists name_mc then (
    measure "Boot interpreter" "" ("boot run " ^ name_mc) "";
    (*  measure "Miking interpreter" "" ("mi run " ^ name_mc) "";  *)
    measure "Miking compiler" ("mi compile " ^ name_mc) ("./" ^ name) ("rm -f " ^ name);
    (if Sys.file_exists (name ^ ".ml") then (
        measure "OCaml byte code" ("ob " ^ name ^ ".byte")
          ("ocamlrun " ^ name ^ ".byte") ("rm -f " ^ name ^ ".byte");
        measure "OCaml native" ("ob " ^ name ^ ".native")
          (name ^ ".native") ("rm -f " ^ name ^ ".native"))
     else ()))
  else
    printf "ERROR: Cannot find file %s.mc\n" name 
