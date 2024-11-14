
include "option.mc"

type WriteChannel
type ReadChannel


-- Returns true if the give file exists, else false
external externalFileExists ! : String -> Bool
let fileExists = lam s. externalFileExists s

-- Deletes the file from the file system. If the file does not
-- exist, no error is reported. Use function fileExists to check
-- if the file exists.
external externalDeleteFile ! : String -> ()
let fileDeleteFile = lam s. if externalFileExists s then externalDeleteFile s else ()

-- Returns the size in bytes of a given file
-- If the file does not exist, 0 is returned.
-- Use function fileExists to check if a file exists.
external externalFileSize ! : String -> Int
let fileSize : String -> Int =
  lam name. externalFileSize name

-- Open a file for writing. Note that we
-- always open binary channels.
-- Note: the external function is shadowed. Use the second signature
external externalWriteOpen ! : String -> (WriteChannel, Bool)
let fileWriteOpen : String -> Option WriteChannel =
  lam name. match externalWriteOpen name with (wc, true) then Some wc else None ()

-- Write a text string to the output channel
-- Right now, it does not handle Unicode correctly
-- It should default to UTF-8
external externalWriteString ! : WriteChannel -> String -> ()
let fileWriteString : WriteChannel -> String -> () =
  lam c. lam s. externalWriteString c s

-- Flush output channel
external externalWriteFlush ! : WriteChannel -> ()
let fileWriteFlush = lam c. externalWriteFlush c

-- Close a write channel
external externalWriteClose ! : WriteChannel -> ()
let fileWriteClose = lam c. externalWriteClose c

-- Open a file for reading. Read open either return
-- Note: the external function is shadowed. Use the second signature
external externalReadOpen ! : String -> (ReadChannel, Bool)
let fileReadOpen : String -> Option ReadChannel =
  lam name. match externalReadOpen name with (rc, true) then Some rc else None ()

-- Reads one line of text. Returns None if end of file.
-- If a successful line is read, it is returned without
-- the end-of-line character.
-- Should support Unicode in the future.
-- Note: the external function is shadowed. Use the second signature
external externalReadLine ! : ReadChannel -> (String, Bool)
let fileReadLine : ReadChannel -> Option String =
  lam rc. match externalReadLine rc with (s, false) then Some s else None ()

-- Reads everything in a file and returns the content as a string.
-- Should support Unicode in the future.
external externalReadString ! : ReadChannel -> String
let fileReadString = lam c. externalReadString c

-- Closes a channel that was opened for reading
external externalReadClose ! : ReadChannel -> ()
let fileReadClose = lam c. externalReadClose c

-- Standard in read channel
external externalStdin ! : ReadChannel
let fileStdin = externalStdin

-- Standard out write channel
external externalStdout ! : WriteChannel
let fileStdout = externalStdout

-- Standard error write channel
external externalStderr ! : WriteChannel
let fileStderr = externalStderr

mexpr

let filename = "___testfile___.txt" in

-- Test to open a file and write some lines of text
utest
  match fileWriteOpen filename with Some wc then
    let write = fileWriteString wc in
    write "Hello\n";
    write "Next string\n";
    write "Final";
    fileWriteFlush wc; -- Not needed here, just testing the API
    fileWriteClose wc;
    ""
  else "Error writing to file."
with "" in

-- Check that the created file exists
utest fileExists filename with true in

-- Test to open and read the file created above (line by line)
utest
  match fileReadOpen filename with Some rc then
    let l1 = match fileReadLine rc with Some s then s else "" in
    let l2 = match fileReadLine rc with Some s then s else "" in
    let l3 = match fileReadLine rc with Some s then s else "" in
    let l4 = match fileReadLine rc with Some s then s else "EOF" in
    fileReadClose rc;
    (l1,l2,l3,l4)
  else ("Error reading file","","","")
with ("Hello", "Next string", "Final", "EOF") in

-- Check that the file size is correct
utest fileSize filename with 23 in

-- Reads the content of the file using function fileReadString()
utest
  match fileReadOpen filename with Some rc then
    let s = fileReadString rc in
    (s, length s)
  else ("",0)
with ("Hello\nNext string\nFinal", 23) in

-- Delete the newly created file and check that it does not exist anymore
utest
  fileDeleteFile filename;
  fileExists filename
with false in

-- Delete the file, even if it does not exist, and make sure that we do not get an error
utest fileDeleteFile filename with () in

-- Check that we get file size 0 if the file does not exist
utest fileSize filename with 0 in

-- Test to open a file (for reading) that should not exist
utest
  match fileReadOpen "__should_not_exist__.txt" with Some _ then true else false
with false in

-- Test to open a file (for writing) with an illegal file name
utest
  match fileWriteOpen "////" with Some _ then true else false
with false in

-- Tests that stdin, stdout, and stderr are available.
-- Uncomment the lines below to test the echo function in interactive mode.
utest
  let skip = (fileStdin, fileStdout, fileStderr) in
  --match fileReadLine stdin with Some s in
  --fileWriteString stdout s;
  --fileWriteString stderr s;
  ()
with () in

()
