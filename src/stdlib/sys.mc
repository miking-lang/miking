include "string.mc"

type ReturnCode = Int
type ExecResult = {stdout: String, stderr: String, returncode: ReturnCode}

let _pathSep = "/"
let _tempBase = "/tmp"
let _null = "/dev/null"

let sysCommandExists : String -> Bool = lam cmd.
  eqi 0 (command (join ["command -v ", cmd, " >/dev/null 2>&1"]))

utest sysCommandExists "ls" with true

let #var"ASSERT_MKDIR" : () =
  if sysCommandExists "mkdir" then ()
  else error "Couldn't find 'mkdir' on PATH, exiting."

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

let sysCopyFile = lam fromFile. lam toFile.
  _commandList ["cp", "-f", fromFile, toFile]

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

let sysTempMake = lam dir: Bool. lam prefix: String. lam.
  let maxTries = 10000 in
  recursive let mk = lam base. lam i.
    if lti i maxTries then
      let name = concat base (int2string i) in
      match
        _commandList [
          if dir then "mkdir" else "touch",
          sysJoinPath _tempBase name, "2>", _null
        ]
        with 0
      then name
      else mk base (addi i 1)
    else
      error "sysTempMake: Failed to make temporary directory."
  in
  let alphanumStr = create 10 (lam. randAlphanum ()) in
  let base = concat prefix alphanumStr in
  let name = mk base 0 in
  sysJoinPath _tempBase name

let sysTempDirMakePrefix: String -> () -> String = sysTempMake true
let sysTempFileMakePrefix: String -> () -> String = sysTempMake false

let sysTempDirMake: () -> String = sysTempDirMakePrefix "miking-tmp."
let sysTempFileMake: () -> String = sysTempFileMakePrefix "miking-tmp."

let sysTempDirName = lam td. td
let sysTempDirDelete = lam td. lam. sysDeleteDir td

utest
  let d = sysTempDirMake () in
  let exists = sysFileExists (sysTempDirName d) in
  sysTempDirDelete d ();
  [exists, sysFileExists (sysTempDirName d)]
with [true, false]

let sysRunCommandWithTimingTimeoutFileIO
    : Option Float -> [String] -> String -> String -> String -> String
      -> (Float, ReturnCode) =
  lam timeoutSec. lam cmd. lam stdinFile.
  lam stdoutFile. lam stderrFile. lam cwd.
    let fullCmd =
    [ "cd", cwd, ";"
    , strJoin " " cmd
    , ">", stdoutFile
    , "2>", stderrFile
    , "<", stdinFile
    , ";"
    ] in
    let fullCmd =
      match timeoutSec with Some timeout then
        _commandListTimeoutWrap timeout fullCmd
      else fullCmd
    in
    match _commandListTime fullCmd with (ms, retCode) then
      (ms, retCode)
    else never

let sysRunCommandWithTimingTimeout : Option Float -> [String] -> String -> String -> (Float, ExecResult) =
  lam timeoutSec. lam cmd. lam stdin. lam cwd.
    let tempDir = sysTempDirMake () in
    let tempStdin = sysJoinPath tempDir "stdin.txt" in
    writeFile tempStdin stdin;
    let tempStdout = sysJoinPath tempDir "stdout.txt" in
    let tempStderr = sysJoinPath tempDir "stderr.txt" in
    let res = sysRunCommandWithTimingTimeoutFileIO
                timeoutSec cmd tempStdin tempStdout tempStderr cwd in
    -- NOTE(Linnea, 2021-04-14): Workaround for readFile bug #145
    _commandList ["echo", "", ">>", tempStdout];
    _commandList ["echo", "", ">>", tempStderr];
    let stdout = init (readFile tempStdout) in
    let stderr = init (readFile tempStderr) in
    sysTempDirDelete tempDir ();
    (res.0, {stdout = stdout, stderr = stderr, returncode = res.1})

utest sysRunCommandWithTimingTimeout (None ()) ["echo -n \"\""] "" "."; () with ()

let sysRunCommandWithTimingFileIO : [String] -> String -> String -> String -> String -> (Float, ReturnCode) =
  sysRunCommandWithTimingTimeoutFileIO (None ())

let sysRunCommandWithTiming : [String] -> String -> String -> (Float, ExecResult) =
    sysRunCommandWithTimingTimeout (None ())

let sysRunCommandFileIO : [String] -> String -> String -> String -> String -> ReturnCode =
  lam cmd. lam stdinFile. lam stdoutFile. lam stderrFile. lam cwd.
    match sysRunCommandWithTimingFileIO cmd stdinFile stdoutFile stderrFile cwd
    with (_, res) then res else never

let sysRunCommand : [String] -> String -> String -> ExecResult =
  lam cmd. lam stdin. lam cwd.
    match sysRunCommandWithTiming cmd stdin cwd with (_, res) then res else never

let sysGetCwd : () -> String = lam. strTrim (sysRunCommand ["pwd"] "" ".").stdout

let sysGetEnv : String -> Option String = lam env.
  let res = strTrim (sysRunCommand ["echo", concat "$" env] "" ".").stdout in
  if null res then None ()
  else Some res

let sysAppendFile : String -> String -> ReturnCode =
  lam filename. lam str.
  let f = sysTempFileMake () in
  writeFile f str;
  let r = _commandList ["cat", f, ">>", filename] in
  sysDeleteFile f;
  r
