-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines a simple language fragment CSV for reading and writing data in CSV
-- format.

include "string.mc"

lang CSV
  syn CSVRow =

  sem csvHeader : CSVRow -> [String]

  sem csvRow2string : CSVRow -> [String]

  sem csvString2Row : [String] -> CSVRow

  sem csvWrite : String -> [CSVRow] -> String
  sem csvWrite sep =
  | rows ->
    match rows with [] then ""
    else
      let header: String = strJoin sep (csvHeader (head rows)) in
      let strRows: [[String]] = map csvRow2string rows in
      let strRowsSep: [String] = map (strJoin sep) strRows in
      let str = cons header strRowsSep in
      concat (strJoin "\n" str) "\n"

  sem csvRead : ([String] -> CSVRow) -> String -> Bool -> String -> [CSVRow]
  sem csvRead string2row sep header =
  | str ->
    let rows: [String] = strSplit "\n" (strTrim str) in
    let rows: [[String]] = map (strSplit sep) rows in
    match rows with [] then []
    else
      let rows = if header then tail rows else rows in
      map string2row rows
end

lang _testCSV = CSV
  syn CSVRow =
  | Data {col1: Int, col2: Float}

  sem csvRow2string =
  | Data {col1 = col1, col2 = col2} ->
    [ int2string col1
    , float2string col2
    ]

  sem csvHeader =
  | Data {col1 = col1, col2 = col2} ->
    [ "col1"
    , "col2"
    ]

  sem csvString2Row =
  | row ->
    Data {col1 = string2int (get row 0),
          col2 = string2float (get row 1)}
end

mexpr

use _testCSV in

let data = [Data {col1 = 1, col2 = 0.}, Data {col1 = 4, col2 = 3.14}] in

utest csvWrite "," data with
"col1,col2
1,0.
4,3.14
" in

utest csvWrite ";" data with
"col1;col2
1;0.
4;3.14
" in

utest csvRead csvString2Row "," true
"
col1,col2
1,0.
4,3.14

" with [Data {col1 = 1, col2 = 0.}, Data {col1 = 4, col2 = 3.14}]
in

utest csvRead csvString2Row ";" false
"

1;0.
4;3.14

" with [Data {col1 = 1, col2 = 0.}, Data {col1 = 4, col2 = 3.14}]
in

()
