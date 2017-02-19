

open Printf

let doPrint = false
  
let filename = "f.txt"

let buf_size = 32768

let rec counting count buf s i =
  if i < s then
    let count = if Bytes.get buf i = ',' then count + 1 else count in
    counting count buf s (i+1) 
  else count
  
let main = 
  let f = open_in_bin filename in
  let buf = Bytes.create buf_size in
  let fsize = in_channel_length f in
  let rec readinput i count =
    if i < fsize then
      let s = min buf_size (fsize - i) in
      let _ = input f buf 0 s in
      readinput (i+buf_size) (counting count buf s 0)
    else count
  in
  let count = readinput 0 0 in
  close_in f;
  if doPrint then printf "count = %d\n" count else ()


