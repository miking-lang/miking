include "string.mc"

type ExecResult = {stdout: String, stderr: String, returncode: Int}

let _pathSep = "/"
let _tempBase = "/tmp"
let _null = "/dev/null"

let _tempIdx = ref 0

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

let sysFileExists: String -> Bool = lam file.
  if eqi (_commandList ["test", "-e", file]) 0 then true else false

let sysMoveFile = lam fromFile. lam toFile.
  _commandList ["mv", "-f", fromFile, toFile]

let sysDeleteFile = lam file.
  _commandList ["rm", "-f", file]

let sysDeleteDir = lam dir.
  _commandList ["rm", "-rf", dir]

let sysChmodWriteAccessFile = lam file.
  _commandList ["chmod", "+w", file]

let sysJoinPath = lam p1. lam p2.
  strJoin _pathSep [p1, p2]

let sysTempMake = lam dir: Bool. lam.
  recursive let mk = lam base. lam i.
    let name = concat base (int2string i) in
    match
      _commandList [
        if dir then "mkdir" else "touch",
        sysJoinPath _tempBase name, "2>", _null
      ]
    with 0
    then (addi i 1, name)
    else mk base (addi i 1) in
  match mk "tmp" (deref _tempIdx) with (i, name) then
    modref _tempIdx i;
    sysJoinPath _tempBase name
  else never

let sysTempDirMake = sysTempMake true
let sysTempFileMake = sysTempMake false

let sysTempDirName = lam td. td
let sysTempDirDelete = lam td. lam. sysDeleteDir td

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

let sysGetCwd : () -> String = lam. strTrim (sysRunCommand ["pwd"] "" ".").stdout

let sysGetEnv : String -> Option String = lam env.
  let res = strTrim (sysRunCommand ["echo", concat "$" env] "" ".").stdout in
  if null res then None ()
  else Some res

utest sysCommandExists "ls" with true
