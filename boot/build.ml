(* 
   Modelyze II is licensed under the MIT license.  
   Copyright (C) David Broman. See file LICENSE.txt

   General build script written in Ocaml so that it becomes platform
   independent (no need to install Make on Windows).
*)


open Printf
open Sys


(* Handle directories *)
let startdir = getcwd()
let maindir() = chdir startdir

let rmfiles s =
  let _ = command ((if win32 then "del /q " else "rm -f ") ^ s) in ()

let cleanup_files() =
  maindir();
  chdir "boot";
  rmfiles "*.cmi *.cmx *.o lexer.ml parser.ml parser.mli";
  maindir()

(* Execute a shell command. Exit if there is an error *)
let cmd s =
  let code = command s in
  if code != 0 then (cleanup_files(); exit code) else ()


let sl = if win32 then "\\" else "/"
  
let dir_exists s =
  try is_directory s with _ -> false

let mkdir s =
  if not (dir_exists s) then
  cmd ("mkdir " ^ s) else ()

let rmdir s =
  if win32 then
    if dir_exists s then
      cmd ("rmdir /s /q " ^ s)
    else ()
  else
    cmd ("rm -rf " ^ s)

let lsdir2file dir targetfile =
  if win32 then
    cmd ("dir " ^ dir ^ " > " ^ targetfile)  
  else (* unix. Might now work on Linux *)
    if command ("ls -l -T " ^ dir ^ " > " ^ targetfile ^ " 2>/dev/null") != 0
    then cmd ("ls --full-time " ^ dir ^ " > " ^ targetfile)

let read_binfile filename =
  let f = open_in_bin filename in
  let size = in_channel_length f in
  let s = Bytes.create size in
  try 
    let rec readinput pos size =
      let read = input f s pos size in
      if read != 0 then readinput (pos+read) (size-read) else ()
    in
    readinput 0 size;
    close_in f; 
    s 
  with 
  | Invalid_argument _ -> raise (Sys_error "Cannot read file")
      

let should_recompile_bootstrapper() =
  if win32 then true else
  let file =  "bin" ^ sl ^ "_bootbuildtag" in
  if not (file_exists file) then (
    lsdir2file "boot" file;
    true)
  else
    let s1 = read_binfile file in
    lsdir2file "boot" file;
    let s2 = read_binfile file in
    s1 <> s2
        
let build_bootstrapper() =
  if should_recompile_bootstrapper() then (
    printf "Building bootstrapper...\n";
    flush_all();
    chdir "boot";
    cmd "ocamllex lexer.mll";
    cmd "ocamlyacc parser.mly";
    cmd ("ocamlopt -o .." ^ sl ^ "bin" ^ sl ^ "mozboot utils.mli utils.ml " ^
          "ustring.mli ustring.ml msg.ml ast.ml parser.mli lexer.ml " ^
          "parser.ml mozboot.ml"))
  else
    printf "The bootstrapper is already up to date.\n"
  
      
(************************************************************)  
(* The build script for building all components of Modelyze *)
let build() =
  mkdir "bin";
  build_bootstrapper();
  cleanup_files();
  maindir();
  printf "Build complete.\n";
  flush_all()
  

    
(************************************************************)  
(* Cleaning all build data *)
let clean() =
  rmdir "bin";
  cleanup_files();
  printf "Cleaning complete.\n"

    
(************************************************************)    
(* Script for performing tests *)     
let test() =
  cmd ("bin" ^ sl ^ "mozboot test test" ^ sl ^ "boot")    

    
(************************************************************)  
(* Main program. Check arguments *)
let main =
  if Array.length argv = 1 then
  (* Build script for making a complete build *)
    build()
  else if argv.(1) = "clean" then 
  (* Script for cleaning all build data *)
    clean()
  else if argv.(1) = "test" then (
  (* Script for doing regression testing *)
    build();
    test())
  else
  (* Show error message *)  
    printf "Unknown argument '%s'\n" argv.(1)









      
