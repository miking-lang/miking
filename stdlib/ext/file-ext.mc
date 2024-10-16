
include "option.mc"

type WriteChannel
type ReadChannel


-- Returns true if the give file exists, else false
external fileExists ! : String -> Bool

-- Deletes the file from the file system. If the file does not
-- exist, no error is reported. Use function fileExists to check
-- if the file exists.
external deleteFile ! : String -> ()
let deleteFile = lam s. if fileExists s then deleteFile s else ()

-- Returns the size in bytes of a given file
-- If the file does not exist, 0 is returned.
-- Use function fileExists to check if a file exists.
external fileSize ! : String -> Int

-- Open a file for writing. Note that we
-- always open binary channels.
-- Note: the external function is shadowed. Use the second signature
external writeOpen ! : String -> (WriteChannel, Bool)
let writeOpen : String -> Option WriteChannel =
  lam name. match writeOpen name with (wc, true) then Some wc else None ()

-- Write a text string to the output channel
-- Right now, it does not handle Unicode correctly
-- It should default to UTF-8
external writeString ! : WriteChannel -> String -> ()
let writeString : WriteChannel -> String -> () =
  lam c. lam s. writeString c s

-- Flush output channel
external writeFlush ! : WriteChannel -> ()

-- Close a write channel
external writeClose ! : WriteChannel -> ()

-- Open a file for reading. Read open either return
-- Note: the external function is shadowed. Use the second signature
external readOpen ! : String -> (ReadChannel, Bool)
let readOpen : String -> Option ReadChannel =
  lam name. match readOpen name with (rc, true) then Some rc else None ()

-- Reads one line of text. Returns None if end of file.
-- If a successful line is read, it is returned without
-- the end-of-line character.
-- Should support Unicode in the future.
-- Note: the external function is shadowed. Use the second signature
external readLine ! : ReadChannel -> (String, Bool)
let readLine : ReadChannel -> Option String =
  lam rc. match readLine rc with (s, false) then Some s else None ()

-- Reads a given number of bytes from the file.
-- Returns None if there is no more content and end of file.
external readBytes ! : ReadChannel -> Int -> (String, Bool)
let readBytes : ReadChannel -> Int -> Option String =
  lam rc. lam len. switch readBytes rc len
    case ("", true) then None ()
    case (s, _) then Some s
  end

-- Reads everything in a file and returns the content as a string.
-- Should support Unicode in the future.
external readString ! : ReadChannel -> String

-- Closes a channel that was opened for reading
external readClose ! : ReadChannel -> ()

-- Standard in read channel
external stdin ! : ReadChannel

-- Standard out write channel
external stdout ! : WriteChannel

-- Standard error write channel
external stderr ! : WriteChannel




mexpr

let filename = "___testfile___.txt" in

-- Test to open a file and write some lines of text
utest
  match writeOpen filename with Some wc then
    let write = writeString wc in
    write "Hello\n";
    write "Next string\n";
    write "Final";
    writeFlush wc; -- Not needed here, just testing the API
    writeClose wc;
    ""
  else "Error writing to file."
with "" in

-- Check that the created file exists
utest fileExists filename with true in

-- Test to open and read the file created above (line by line)
utest
  match readOpen filename with Some rc then
    let l1 = match readLine rc with Some s then s else "" in
    let l2 = match readLine rc with Some s then s else "" in
    let l3 = match readLine rc with Some s then s else "" in
    let l4 = match readLine rc with Some s then s else "EOF" in
    readClose rc;
    (l1,l2,l3,l4)
  else ("Error reading file","","","")
with ("Hello", "Next string", "Final", "EOF") in

-- Test reading x amount of characters from the file
utest
  match readOpen filename with Some rc then
    let l1 = match readBytes rc 3 with Some s in s in
    let l2 = match readBytes rc 4 with Some s in s in
    let l3 = match readBytes rc 0 with Some s in s in
    let l4 = match readBytes rc 1 with Some s in s in
    let l5 = match readBytes rc 1000 with Some s in s in
    let _end = match readBytes rc 1000 with None () in () in
    let _end = match readBytes rc 1000 with None () in () in
    readClose rc;
    (l1,l2,l3,l4,l5)
  else error "Error reading file"
with ("Hel", "lo\nN", "", "e", "xt string\nFinal") in

-- Check that the file size is correct
utest fileSize filename with 23 in

-- Reads the content of the file using function readString()
utest
  match readOpen filename with Some rc then
    let s = readString rc in
    (s, length s)
  else ("",0)
with ("Hello\nNext string\nFinal", 23) in

-- Delete the newly created file and check that it does not exist anymore
utest
  deleteFile filename;
  fileExists filename
with false in

-- Delete the file, even if it does not exist, and make sure that we do not get an error
utest deleteFile filename with () in

-- Check that we get file size 0 if the file does not exist
utest fileSize filename with 0 in

-- Test to open a file (for reading) that should not exist
utest
  match readOpen "__should_not_exist__.txt" with Some _ then true else false
with false in

-- Test to open a file (for writing) with an illegal file name
utest
  match writeOpen "////" with Some _ then true else false
with false in

-- Tests that stdin, stdout, and stderr are available.
-- Uncomment the lines below to test the echo function in interactive mode.
utest
  let skip = (stdin, stdout, stderr) in
  --match readLine stdin with Some s in
  --writeString stdout s;
  --writeString stderr s;
  ()
with () in

()
