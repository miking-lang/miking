-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "string.mc"

-- Data type of info terms
type Info
con Info : {filename: String, row1: Int, col1: Int, row2: Int, col2: Int} -> Info
con NoInfo : () -> Info

let testinfo_: Info = Info {filename = "testinfo_", row1 = 1, col1 = 5, row2 = 1, col2 = 10}

-- Data structure for a positon value
type Pos = {filename: String, row: Int, col: Int}

-- Crate init position, start of file
let initPos : String -> Pos = lam filename.
  {filename = filename, row = 1, col = 0}

-- Create a positon value
let posVal : String -> Int -> Int -> Pos = lam filename. lam row. lam col.
  {filename = filename, row = row, col = col}

-- Advance the column with parameter n
let advanceCol : Pos -> Int -> Pos = lam p : Pos. lam n.
  {p with col = addi p.col n}

-- Advance the positon with parameter n. Set col to zero.
let advanceRow : Pos -> Int -> Pos = lam p : Pos. lam n.
  {{p with row = addi p.row n} with col = 0}

-- Compose an info strucutre from two positions
let makeInfo : Pos -> Pos -> Info = lam p1 : Pos. lam p2 : Pos.
  Info {filename = p1.filename, row1 = p1.row, col1 = p1.col,
        row2 = p2.row, col2 = p2.col}

-- Compose an info structure from two other info structures
let mergeInfo : Info -> Info -> Info = lam fi1 : Info. lam fi2 : Info.
  match fi1 with Info r1 then
    match fi2 with Info r2 then
      Info {filename = r1.filename, row1 = r1.row1, col1 = r1.col1,
            row2 = r2.row2, col2 = r2.col2}
    else fi1
  else fi2

-- Create an info structure
let infoVal : String -> Int -> Int -> Int -> Int -> Info =
  lam filename. lam r1. lam c1. lam r2. lam c2.
  Info {filename = filename, row1 = r1, col1 = c1, row2 = r2, col2 = c2}

-- Generate a string from an info
let info2str : Info -> String = lam fi.
  match fi with NoInfo () then "[No file info] " else
  match fi with Info r then
    join ["FILE \"", r.filename, "\" ", int2string r.row1, ":", int2string r.col1,
    "-", int2string r.row2, ":", int2string r.col2, " "]
  else never

-- Parse an info string into an info
let str2info : String -> Info = lam str.
  let errorNotAnInfo = lam.
    error (join ["Not an info string: '", str, "'"])
  in
  let str = strTrim str in
  match str with "[No file info]" then NoInfo ()
  else
    match strSplit " " str with ["FILE", filename, rowcols] then
      let filename =
        match filename with ['\"'] ++ filename ++ ['\"'] then filename
        else errorNotAnInfo ()
      in
      let parseRowCol : String -> (Int, Int) = lam rowcol.
        match strSplit ":" rowcol with [row, col] then
          (string2int row, string2int col)
        else errorNotAnInfo ()
      in
      match strSplit "-" rowcols with [rowcols1, rowcols2] then
        match (parseRowCol rowcols1, parseRowCol rowcols2)
        with ((row1, col1), (row2, col2)) then
          Info { filename = filename
               , row1 = row1, col1 = col1
               , row2 = row2, col2 = col2
               }
        else never
      else errorNotAnInfo ()
    else errorNotAnInfo ()

utest str2info "   [No file info] " with NoInfo ()
utest str2info "FILE \"path/to/file.mc\" 123:3-124:4"
with Info { filename = "path/to/file.mc",
            row1 = 123, col1 = 3, row2 = 124, col2 = 4 }

-- Generate an info error string
let infoErrorString : Info -> String -> String = lam fi. lam str.
    join [info2str fi, "ERROR: ", str]

-- Print an error with info struct info and exit (error code 1)
let infoErrorExit : Info -> String -> Unknown = lam fi. lam str.
  print (join ["\n", (infoErrorString fi str), "\n"]);
  exit 1

-- Print an error with position info and exit (error code 1)
let posErrorExit : Pos -> String -> Unknown = lam p : Pos. lam str.
  infoErrorExit (infoVal p.filename p.row p.col p.row p.col) str

-- Comparison function for info struct
let infoCmp : Info -> Info -> Int = lam i1. lam i2.
  cmpString (info2str i1) (info2str i2)
