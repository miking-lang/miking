include "string.mc"
include "common.mc"

type ExecResult = {stdout: String, stderr: String, returncode: Int}

let _pathSep = "/"
let _tempDirBase = "/tmp"
let _null = "/dev/null"

let _tempDirIdx = ref 0

let _commandList = lam cmd : [String].
  command (strJoin " " cmd)

let sysMoveFile = lam fromFile. lam toFile.
  _commandList ["mv", "-f", fromFile, toFile]

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

let sysRunCommand : [String] -> String -> String -> ExecResult =
  lam cmd. lam stdin. lam cwd.

    let tempDir = sysTempDirMake () in
    let tempStdout = sysJoinPath tempDir "stdout.txt" in
    let tempStderr = sysJoinPath tempDir "stderr.txt" in

    let retCode = _commandList
      [ "cd", cwd, "&&"
      , "echo", stdin, "|"
      , strJoin " " cmd
      , ">", tempStdout
      , "2>", tempStderr
      ] in

    -- NOTE(Linnea, 2021-04-14): Workaround for readFile bug #145
    _commandList ["echo", "", ">>", tempStdout];
    _commandList ["echo", "", ">>", tempStderr];
    let stdout = init (readFile tempStdout) in
    let stderr = init (readFile tempStderr) in

    sysTempDirDelete tempDir ();

    {stdout = stdout, stderr = stderr, returncode = retCode}
