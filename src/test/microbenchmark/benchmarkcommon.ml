(* let _ = printf "\n** %d **\n" (int_of_string (Arrray.get Sys.argv 1))  *)

let repeat f =
  let rec work f n =
    if n = 0 then ()
    else
      let _ = f () in
      work f (n - 1)
  in
  work f (int_of_string Sys.argv.(1))
