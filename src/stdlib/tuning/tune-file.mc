
include "context-expansion.mc"
include "string.mc"

-- Defines helpers for writing to and reading from a tune file.

type TuneFileFormat
con CSV : () -> TuneFileFormat
con TOML : () -> TuneFileFormat

let _listOfStrings = lam strs.
  join [strJoin ">" strs]

let _delim = "\n"

let _sepLength = 20

let tuneFileIndexStr = "index"
let tuneFileTypeStr = "type"
let tuneFileValueStr = "value"
let tuneFileHoleNameStr = "hole_name"
let tuneFileHoleInfoStr = "hole_info"
let tuneFileFunNameStr = "function_name"
let tuneFileFunInfoStr = "function_info"
let tuneFilePathNameStr = "call_path_functions"
let tuneFilePathInfoStr = "call_path_infos"

let tuneFileIndexIdx = 0
let tuneFileTypeIdx = 1
let tuneFileValueIdx = 2
let tuneFileHoleNameIdx = 3
let tuneFileHoleInfoIdx = 4
let tuneFileFunNameIdx = 5
let tuneFileFunInfoIdx = 6
let tuneFilePathNameIdx = 7
let tuneFilePathInfoIdx = 8

let boolTypeValue = 0
let intTypeValue = 1

let tuneFileExtension = ".tune"

let tuneFileName = lam file.
  let withoutExtension =
  match strLastIndex '.' file with Some idx then
    subsequence file 0 idx
  else file
in concat withoutExtension tuneFileExtension

let _vertexPath : NameInfo -> Int -> CallCtxEnv -> [NameInfo] = lam h : NameInfo. lam i : Int. lam env : CallCtxEnv.
  match env with {verbosePath = verbosePath, hole2fun = hole2fun} then
    let edgePath = mapFindExn i verbosePath in
    match edgePath with [] then
      [mapFindExn h hole2fun]
    else
      let lastEdge : (NameInfo, NameInfo, NameInfo) = last edgePath in
      let destination = lastEdge.1 in
      snoc (map (lam e : (NameInfo, NameInfo, NameInfo). e.0) edgePath)
      destination
  else never

let _tuneTable2str = lam env: CallCtxEnv. lam table : LookupTable.
  use HoleAst in
  let rows = mapi (lam i. lam expr.
    join [int2string i, ": ", int2string (toInt expr (get env.idx2hole i))]) table in
  strJoin _delim rows

let tuneFileDump = lam env : CallCtxEnv. lam table : LookupTable. lam format : TuneFileFormat.
  let hole2idx = env.hole2idx in
  let hole2fun = env.hole2fun in
  let verbosePath = env.verbosePath in
  let callGraph = env.callGraph in

  let entry2str = lam holeInfo : NameInfo. lam path : [NameInfo]. lam i : Int.
    let funInfo : NameInfo = mapFindExn holeInfo hole2fun in
    let path = _vertexPath holeInfo i env in
    let value = get table i in
    let tyAndVal : (Int, String) = use MExprAst in
      match value with TmConst {val = CBool {val = b}} then (boolTypeValue, if b then "true" else "false")
      else match value with TmConst {val = CInt {val = i}} then (intTypeValue, int2string i)
      else error "unknown value type"
    in
    let values =
    [ int2string i
    , int2string tyAndVal.0
    , tyAndVal.1
    , nameInfoGetStr holeInfo
    , info2str holeInfo.1
    , nameInfoGetStr funInfo
    , info2str funInfo.1
    , _listOfStrings (map nameInfoGetStr path)
    , _listOfStrings (map (lam x : NameInfo. info2str x.1) path)
    ] in
    match format with CSV _ then
      strJoin "," values
    else match format with TOML _ then
      strJoin "\n" (zipWith (lam x. lam y. join [x, " = ", y])
        [ tuneFileIndexStr
        , tuneFileTypeStr
        , tuneFileValueStr
        , tuneFileHoleNameStr
        , tuneFileHoleInfoStr
        , tuneFileFunNameStr
        , tuneFileFunInfoStr
        , tuneFilePathNameStr
        , tuneFilePathInfoStr
        ]
        values)
    else never
  in
  let taggedEntries =
    mapFoldWithKey
      (lam acc : [(Int, String)]. lam h : NameInfo. lam pathMap : Map [NameInfo] Int.
         concat acc (map (lam b : ([NameInfo], Int). (b.1, entry2str h b.0 b.1)) (mapBindings pathMap)))
      [] hole2idx
  in
  let sortedTagged =
    sort (lam e1 : (Int, String). lam e2 : (Int, String). subi e1.0 e2.0)
      taggedEntries
  in
  let entries = map (lam e : (Int, String). e.1) sortedTagged in
  match format with CSV _ then
    strJoin "\n" entries
  else match format with TOML _ then
    concat "[[hole]]\n" (strJoin (join ["\n", "[[hole]]", "\n"]) entries)
  else never

let tuneFileDumpTable
= lam file: String. lam env: CallCtxEnv. lam table: LookupTable. lam verbose: Bool.
  let str =
  join
  [ int2string (length table)
  , "\n"
  , _tuneTable2str env table
  , "\n"
  , make _sepLength '='
  , "\n"
  , if verbose then tuneFileDump env table (CSV ()) else ""
  , "\n"
  ] in writeFile file str

let tuneFileReadTable : String -> LookupTable = lam file.
  use BootParser in
  let fileContent = readFile file in
  let rows = strSplit "\n" fileContent in
  let n = string2int (head rows) in
  let strVals = subsequence rows 1 n in
  let strVals = map (lam x. get (strSplit ": " x) 1) strVals in
  map (parseMExprStringKeywordsExn []) strVals
