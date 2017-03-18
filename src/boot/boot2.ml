(* 
   Modelyze II is licensed under the MIT license.  
   Copyright (C) David Broman. See file LICENSE.txt

   boot2.ml is the main entry point for the second stage of the 
   bootstrapped Modelyze compiler. Stage two is using OCaml for
   parsing, but the compiler is implemented in Miking. 
*)

open Utils
open Ustring.Op
open Printf
open Ast
open Msg


let utest = ref false           (* Set to true if unit testing is enabled *)
let compile = ref false         (* Set to true if we should compile instead of run *)
  
(* Print out main menu *)    
let menu() =
  printf "Usage: boot2 [run|test|compile] <files>\n";
  printf "\n"


(* Main function. Checks arguments and reads file names *)
let main =
  if Array.length Sys.argv < 2 then menu()
  else
    (* Check if we should run the test suite *)
    let args =
      let lst = Array.to_list Sys.argv |> List.tl in
      (match List.hd lst with
       | "run" -> List.tl lst
       | "test" | "t" -> utest := true; List.tl lst
       | "compile" | "c" -> compile := true; List.tl lst
       | _ -> lst)
    in
    
    (* Expand folders to file names *)
    let _ = files_of_folders args in
    
    ()

      
    



