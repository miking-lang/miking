-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "string.mc"

-- Data type of info terms
type Info
con Info : {filename: String, row1: Int, col1: Int, row2: Int, col2: Int} -> Info
con NoInfo : () -> Info

-- Data structure for a positon value
type Pos = {filename: String, row: Int, col: Int}

-- Crate init position, start of file
let initPos : String -> Pos = lam filename.
  {filename = filename, row = 1, col = 0}

-- Create a positon value
let posVal : String -> Int -> Int = lam filename. lam row. lam col.
  {filename = filename, row = row, col = col}

-- Advance the column with parameter n
let advanceCol : Pos -> Int -> Pos = lam p. lam n.
  {p with col = addi p.col n}

-- Advance the positon with parameter n. Set col to zero.
let advanceRow : Pos -> Int -> Pos = lam p. lam n.
  {{p with row = addi p.row n} with col = 0}

-- Compose an info strucutre from two positions
let makeInfo : Pos -> Pos -> Info = lam p1. lam p2.
  Info {filename = p1.filename, row1 = p1.row, col1 = p1.col,
        row2 = p2.row, col2 = p2.col}

-- Create an info structure
let infoVal : String -> Int -> Int -> Int -> Int =
  lam filename. lam r1. lam c1. lam r2. lam c2.
  Info {filename = filename, row1 = r1, col1 = c1, row2 = r2, col2 = c2}

-- Generate an info error stirng
let infoErrorString : Info -> String -> String = lam fi. lam str.
  let infoStr =
    match fi with NoInfo () then "[No file info] " else
    match fi with Info r then
      join ["FILE \"", r.filename, "\" ", int2string r.row1, ":", int2string r.col1,
            "-", int2string r.row2, ":", int2string r.col2, " "]
    else never
  in
    join [infoStr, "ERROR: ", str]

-- Print an error with info struct info and exit (error code 1)
let infoErrorExit : Info -> String -> () = lam fi. lam str.
  let _ = print (join ["\n", (infoErrorString fi str), "\n"]) in
  exit 1

-- Print an error with position info and exit (error code 1)
let posErrorExit : Pos -> String -> () = lam p. lam str.
  infoErrorExit (infoVal p.filename p.row p.col p.row p.col) str
