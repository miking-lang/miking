
include "option.mc"

type WriteChannel
type ReadChannel

-- Returns true if the give file exists, else false
--external fileExists ! : String -> Bool

-- Returns the size in bytes of a given file
-- If the file does not exist, 0 is returned.
-- Use function fileExists to check if a file exists.
--external fileSize ! : String -> Int

-- Open a file for writing. Note that we
-- always open binary channels
external writeOpen ! : String -> WriteChannel

-- Write a text string to the output channel
-- Right now, it does not handle Unicode correctly
-- It should default to UTF-8
external writeString ! : WriteChannel -> String -> Unit
let writeString = lam c. lam s. writeString c s

-- Flush output channel
external writeFlush ! : WriteChannel -> Unit

-- Close a write channel
external writeClose ! : WriteChannel -> Unit

-- Open a file for reading.
external readOpen ! : String -> ReadChannel

-- Reads one line of text. Returns None if end of file.
-- If a successful line is read, it is returned without
-- the end-of-line character.
external externalReadLine ! : ReadChannel -> (String, Bool)
let readLine = lam rc. match externalReadLine rc
                       with (s, false) then Some s else None ()

-- Reads everything in a file and returns the content as a string
--external readString ! : ReadChannel -> String

-- Closes a channel that was opened for reading
external readClose ! : ReadChannel -> Unit



external stdin ! : ReadChannel

mexpr

utest
let name = "testfile.txt" in
let wc = writeOpen name  in
writeString wc "Hello\n";
writeString wc "Next string\n";
writeString wc "Final";
writeFlush wc;
writeClose wc;
let rc = readOpen name in
let l1 = match readLine rc with Some s then s else "" in
let l2 = match readLine rc with Some s then s else "" in
let l3 = match readLine rc with Some s then s else "" in
let l4 = match readLine rc with Some s then s else "EOF" in
readClose rc;
(l1,l2,l3,l4)
with ("Hello", "Next string", "Final", "EOF") in



()
