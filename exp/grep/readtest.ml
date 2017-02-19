

open Printf


  
let filename = "f.txt"

let buf_size = 32768

let main = 
  let f = open_in_bin filename in
  let buf = Bytes.create buf_size in
  let fsize = in_channel_length f in
  let rec readinput i =
    if i < fsize then 
      let _ = input f buf 0 (min buf_size (fsize - i)) in      
      readinput (i+buf_size) 
    else ()
  in
  readinput 0;
  close_in f     


