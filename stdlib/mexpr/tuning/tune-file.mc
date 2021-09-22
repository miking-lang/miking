
include "decision-points.mc"
include "string.mc"

type TuneFileFormat
con CSV : () -> TuneFileFormat
con TOML : () -> TuneFileFormat

let _listOfStrings = lam strs.
  join [strJoin ">" strs]

let _delim = "\n"

let _sepLength = 20

let indexStr = "index"
let typeStr = "type"
let valueStr = "value"
let holeNameStr = "hole_name"
let holeInfoStr = "hole_info"
let funNameStr = "function_name"
let funInfoStr = "function_info"
let pathNameStr = "call_path_functions"
let pathInfoStr = "call_path_infos"

let indexIdx = 0
let typeIdx = 1
let valueIdx = 2
let holeNameIdx = 3
let holeInfoIdx = 4
let funNameIdx = 5
let funInfoIdx = 6
let pathNameIdx = 7
let pathInfoIdx = 8

let boolTypeValue = 0
let intTypeValue = 1

let tuneFileExtension = ".tune"

let tuneFileName = lam file.
  let withoutExtension =
  match strLastIndex '.' file with Some idx then
    subsequence file 0 idx
  else file
in concat withoutExtension tuneFileExtension

let _vertexPath : NameInfo -> Int -> Env -> [NameInfo] = lam h : NameInfo. lam i : Int. lam env : CallCtxEnv.
  match env with {verbosePath = verbosePath, hole2fun = hole2fun} then
    let edgePath = mapFindWithExn i (deref verbosePath) in
    match edgePath with [] then
      [mapFindWithExn h (deref hole2fun)]
    else
      let lastEdge : (NameInfo, NameInfo, NameInfo) = last edgePath in
      let destination = lastEdge.1 in
      snoc (map (lam e : (NameInfo, NameInfo, NameInfo). e.0) edgePath)
      destination
  else never

let _tuneTable2str = lam table : LookupTable.
  use MExprPrettyPrint in
  let rows = mapi (lam i. lam expr.
    join [int2string i, ": ", expr2str expr]) table in
  strJoin _delim rows

let tuneFileDump = lam env : CallCtxEnv. lam table : LookupTable. lam format : TuneFileFormat.
  let hole2idx = deref env.hole2idx in
  let hole2fun = deref env.hole2fun in
  let verbosePath = deref env.verbosePath in
  let callGraph = env.callGraph in

  let entry2str = lam holeInfo : NameInfo. lam path : [NameInfo]. lam i : Int.
    let funInfo : NameInfo = mapFindWithExn holeInfo hole2fun in
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
        [ indexStr
        , typeStr
        , valueStr
        , holeNameStr
        , holeInfoStr
        , funNameStr
        , funInfoStr
        , pathNameStr
        , pathInfoStr
        ]
        values)
    else never
  in
  let taggedEntries =
    mapFoldWithKey
      (lam acc : [String]. lam h : NameInfo. lam pathMap : Map [NameInfo] Int.
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

let tuneFileDumpTable = lam file : String. lam env : Option CallCtxEnv. lam table : LookupTable.
  print "dumping to"; printLn file;
  let str =
  join
  [ int2string (length table)
  , "\n"
  , _tuneTable2str table
  , "\n"
  , make _sepLength '='
  , "\n"
  , match env with Some env then tuneFileDump env table (CSV ()) else ""
  , "\n"
  ] in writeFile file str


let tuneFileReadTable : String -> LookupTable = lam file.
  use BootParser in
  let fileContent = readFile file in
  let rows = strSplit "\n" fileContent in
  let n = string2int (head rows) in
  let strVals = subsequence rows 1 n in
  let strVals = map (lam x. get (strSplit ": " x) 1) strVals in
  map (parseMExprString []) strVals
