include "string.mc"

type ExecResult = {stdout: String, stderr: String, returncode: Int}

let _pathSep = "/"
let _tempDir = "/tmp/program"
let _tempStdout = "/tmp/stdout.txt"
let _tempStderr = "/tmp/stderr.txt"

let phMoveFile = lam fromFile. lam toFile.
  command (strJoin " " ["mv -f", fromFile, toFile])

let phChmodWriteAccessFile = lam file.
  command (join ["chmod +w ", file])

let phJoinPath = lam p1. lam p2.
  strJoin _pathSep [p1, p2]

let phRunCommand : [String] -> String -> String -> ExecResult =
  lam cmd. lam stdin. lam cwd.
    let retCode = command (strJoin " "
      [ "cd", cwd, "&&"
      , "echo", stdin, "|"
      , strJoin " " cmd
      , ">", _tempStdout
      , "2>", _tempStderr
      ]) in
    -- NOTE(Linnea, 2021-04-14): Workaround for readFile bug #145
    command (concat "echo \"\" >> " _tempStdout);
    command (concat "echo \"\" >> " _tempStderr);
    let stdout = init (readFile _tempStdout) in
    let stderr = init (readFile _tempStderr) in
    {stdout = stdout, stderr = stderr, returncode = retCode}

let phTempDirMake = lam. command (join ["mkdir -p ", _tempDir])
let phTempDirName = lam. _tempDir
let phTempDirDelete = lam. lam. command (join ["rm -rf ", _tempDir])
