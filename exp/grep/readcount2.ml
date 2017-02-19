

open Printf

let doPrint = true
  
let filename = "f.txt"

let buf_size = 32768

let rec counting lst count =
  match lst with
  | x::xs -> counting xs (if x = int_of_char ',' then count + 1 else count)
  | [] -> count

let rec convert buf s i acc =
  if i < s then
    convert buf s (i+1) ((int_of_char (Bytes.get buf i))::acc)
  else
    List.rev acc
  
    
    
let main = 
  let f = open_in_bin filename in
  let buf = Bytes.create buf_size in
  let fsize = in_channel_length f in
  let rec readinput i count =
    if i < fsize then
      let s = min buf_size (fsize - i) in
      let _ = input f buf 0 s in
      readinput (i+buf_size) (counting (convert buf s 0 []) count)
    else count
  in
  let count = readinput 0 0 in
  close_in f;
  if doPrint then printf "count = %d\n" count else ()


