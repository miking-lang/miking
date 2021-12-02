include "string.mc"

type ExecResult = {stdout: String, stderr: String, returncode: Int}

let _pathSep = "/"
let _tempDirBase = "/tmp"
let _null = "/dev/null"

let _tempDirIdx = ref 0

let _commandListTime : [String] -> (Float, Int) = lam cmd.
  let cmd = strJoin " " cmd in
  let t1 = wallTimeMs () in
  let res = command cmd in
  let t2 = wallTimeMs () in
  (subf t2 t1, res)

let _commandList = lam cmd : [String].
  match _commandListTime cmd with (_, res) then res else never

let _commandListTimeoutWrap : Float -> [String] -> [String] = lam timeoutSec. lam cmd.
  join [ ["timeout", "-k", "0.1", float2string timeoutSec, "bash", "-c", "\'{"]
       , cmd
       , ["\'}"]
       ]

let sysMoveFile = lam fromFile. lam toFile.
  _commandList ["mv", "-f", fromFile, toFile]

let sysDeleteFile = lam file.
  _commandList ["rm", "-f", file]

let sysChmodWriteAccessFile = lam file.
  _commandList ["chmod", "+w", file]

let sysJoinPath = lam p1. lam p2.
  strJoin _pathSep [p1, p2]

let sysTempDirMake = lam.
  recursive let mkdir = lam base. lam i.
    let dirName = concat base (int2string i) in
    match
      _commandList ["mkdir", sysJoinPath _tempDirBase dirName, "2>", _null]
    with 0
    then (addi i 1, dirName)
    else mkdir base (addi i 1) in
  match mkdir "tmp" (deref _tempDirIdx) with (i, dir) then
    modref _tempDirIdx i;
    sysJoinPath _tempDirBase dir
  else never

let sysTempDirName = lam td. td
let sysTempDirDelete = lam td. lam.
  _commandList ["rm", "-rf", td]

let sysRunCommandWithTimingTimeout : Option Float -> [String] -> String -> String -> (Float, ExecResult) =
  lam timeoutSec. lam cmd. lam stdin. lam cwd.
    let tempDir = sysTempDirMake () in
    let tempStdout = sysJoinPath tempDir "stdout.txt" in
    let tempStderr = sysJoinPath tempDir "stderr.txt" in

    let fullCmd =
    [ "cd", cwd, ";"
    , "echo", stdin, "|"
    , strJoin " " cmd
    , ">", tempStdout
    , "2>", tempStderr
    , ";"
    ] in
    let fullCmd =
      match timeoutSec with Some timeout then
        _commandListTimeoutWrap timeout fullCmd
      else fullCmd
    in
    match _commandListTime fullCmd with (ms, retCode) then

      -- NOTE(Linnea, 2021-04-14): Workaround for readFile bug #145
      _commandList ["echo", "", ">>", tempStdout];
      _commandList ["echo", "", ">>", tempStderr];
      let stdout = init (readFile tempStdout) in
      let stderr = init (readFile tempStderr) in

      sysTempDirDelete tempDir ();
      (ms, {stdout = stdout, stderr = stderr, returncode = retCode})
    else never

utest sysRunCommandWithTimingTimeout (None ()) ["echo -n \"\""] "" "."; () with ()

let sysRunCommandWithTiming : [String] -> String -> String -> (Float, ExecResult) =
  lam cmd. lam stdin. lam cwd.
    sysRunCommandWithTimingTimeout (None ()) cmd stdin cwd

let sysRunCommand : [String] -> String -> String -> ExecResult =
  lam cmd. lam stdin. lam cwd.
    match sysRunCommandWithTiming cmd stdin cwd with (_, res) then res else never

let sysCommandExists : String -> Bool = lam cmd.
  eqi 0 (command (join ["which ", cmd, " >/dev/null 2>&1"]))

utest sysCommandExists "ls" with true
