
include "option.mc"

type WriteChannel
type ReadChannel


-- Returns true if the give file exists, else false
external fileExists ! : String -> Bool

-- Deletes the file from the file system. If the file does not
-- exist, no error is reported. Use function fileExists to check
-- if the file exists.
external deleteFile ! : String -> Unit
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
external writeString ! : WriteChannel -> String -> Unit
let writeString : WriteChannel -> String -> Unit =
  lam c. lam s. writeString c s

-- Flush output channel
external writeFlush ! : WriteChannel -> Unit

-- Close a write channel
external writeClose ! : WriteChannel -> Unit

-- Open a file for reading. Read open either return
-- Note: the external function is shadowed. Use the second signature
external readOpen ! : String -> (ReadChannel, Bool)
let readOpen : String -> Option ReadChannel =
  lam name. match readOpen name with (rc, true) then Some rc else None ()

-- Reads one line of text. Returns None if end of file.
-- If a successful line is read, it is returned without
-- the end-of-line character.
-- Note: the external function is shadowed. Use the second signature
external readLine ! : ReadChannel -> (String, Bool)
let readLine : ReadChannel -> Option String =
  lam rc. match readLine rc with (s, false) then Some s else None ()

-- Reads everything in a file and returns the content as a string
--external readString ! : ReadChannel -> String

-- Closes a channel that was opened for reading
external readClose ! : ReadChannel -> Unit



--external stdin ! : ReadChannel

mexpr

-- Test to delete a file that does not exist. Should not give an error.
--utest
--  deleteFile "___cannot_exist__.txt";
--  deleteFile "___cannot_exist__.txt" -- Cannot exist the second time
--with () in

-- Test to open a file and write some lines of text
utest
  match writeOpen "___testfile___.txt" with Some wc then
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
utest fileExists "___testfile___.txt" with true in

-- Test to open and read the file created above (line by line)
utest
  match readOpen "___testfile___.txt" with Some rc then
    let l1 = match readLine rc with Some s then s else "" in
    let l2 = match readLine rc with Some s then s else "" in
    let l3 = match readLine rc with Some s then s else "" in
    let l4 = match readLine rc with Some s then s else "EOF" in
    readClose rc;
    (l1,l2,l3,l4)
  else ("Error reading file","","","")
with ("Hello", "Next string", "Final", "EOF") in

-- Check that the file size is correct
utest fileSize "___testfile___.txt" with 23 in

-- Delete the newly created file and check that it does not exist anymore
utest
  deleteFile "___testfile___.txt";
  fileExists "___testfile___.txt"
with false in

-- Delete the file, even if it does not exist, and make sure that we do not get an error
utest deleteFile "___testfile___.txt" with () in

-- Check that we get file size 0 if the file does not exist
utest fileSize "___testfile___.txt" with 0 in

-- Test to open a file (for reading) that should not exist
utest
  match readOpen "__should_not_exist__.txt" with Some _ then true else false
with false in

-- Test to open a file (for writing) with an illegal file name
utest
  match writeOpen "////" with Some _ then true else false
with false in

()
