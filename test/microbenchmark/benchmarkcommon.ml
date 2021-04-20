
(* let _ = printf "\n** %d **\n" (int_of_string (Arrray.get Sys.argv 1)) *)

let rec repeat f n =
  if n = 0 then () else let _ = f() in repeat f (n - 1)


