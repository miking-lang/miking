include "string.mc"

type ExecResult = {stdout: String, stderr: String, returncode: Int}

let _pathSep = "/"
let _tempDirBase = "/tmp"
let _null = "/dev/null"

let phMoveFile = lam fromFile. lam toFile.
  command (strJoin " " ["mv -f", fromFile, toFile])

let phChmodWriteAccessFile = lam file.
  command (join ["chmod +w ", file])

let phJoinPath = lam p1. lam p2.
  strJoin _pathSep [p1, p2]

let phTempDirMake = lam.
  recursive let mkdir = lam base. lam i.
    let dirName = concat base (int2string i) in
    match
      command (strJoin " " ["mkdir", phJoinPath _tempDirBase dirName,
                            "2>", _null])
    with 0
    then dirName
    else mkdir base (addi i 1)
  in phJoinPath _tempDirBase (mkdir "tmp" 0)

let phTempDirName = lam td. td
let phTempDirDelete = lam td. lam.
  command (join ["rm -rf ", td])

let phRunCommand : [String] -> String -> String -> ExecResult =
  lam cmd. lam stdin. lam cwd.
    let tempDir = phTempDirMake () in
    let tempStdout = phJoinPath tempDir "stdout.txt" in
    let tempStderr = phJoinPath tempDir "stdout.txt" in 

    let retCode = command (strJoin " "
      [ "cd", cwd, "&&"
      , "echo", stdin, "|"
      , strJoin " " cmd
      , ">", tempStdout
      , "2>", tempStderr
      ]) in

    -- NOTE(Linnea, 2021-04-14): Workaround for readFile bug #145
    command (concat "echo \"\" >> " tempStdout);
    command (concat "echo \"\" >> " tempStderr);
    let stdout = init (init (readFile tempStdout)) in
    let stderr = init (init (readFile tempStderr)) in

    phTempDirDelete tempDir ();

    {stdout = stdout, stderr = stderr, returncode = retCode}
