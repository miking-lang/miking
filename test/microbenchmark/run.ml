
open Printf


    
let _ =      
  printf "%f\n" (l2 -. l1)

let measure str pre_cmd cmd post_cmd =
  let _ = Sys.command pre_cmd in
  let l1 = Sys.time() in
  let _ = Sys.command cmd in
  let l2 = Sys.time() in
  let _ = Sys.command post_cmd in
  printf "%s: %fs\n" str (l2 -. l1)


let main =
  if Array.length Sys.argv = 2 then
    let name = Array.get Sys.argv 1 in
    if Sys.command ("ls " ^ name ^ ".mc") = 0 then
      let name_mc = name ^ ".mc" in
      measure "Boot interpreter" "" ("boot run " ^ name ^ ".mc");
      measure "Miking interpreter" "" ("mi run " ^ name ^ ".mc"); 
      measure "Miking compiler" ("mi compile " ^ name ^ ".mc") ("./" ^ name) ("rm -f" ^ name)
  else
      printf "ERROR: Cannot find file %s.mc\n" name 
  else
    printf "Usage: run [benchmark-name-without-postfix-name]\nExample: run factorial\n\n"
