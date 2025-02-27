include "ext/file-ext.mc"

let stripUriProtocol = lam uri. match uri
  with "file://" ++ rest then rest
  else uri

-- BEGIN IO --

-- returns Option content if the requested number of bytes could be read
-- otherwise, None is returned
let readBytesBuffered : ReadChannel -> Int -> Option [Int] =
  lam rc. lam len.
  recursive let work = lam remainLen. lam acc.
    if leqi remainLen 0 then Some acc
    else switch fileReadBytes rc remainLen
      case Some s then
        let acc = concat acc s in
        let readLen = length s in
        work (subi remainLen readLen) acc
      case None () then None ()
    end
  in work len []

let eprint: String -> () = lam s.
  fileWriteString fileStderr s;
  flushStderr()

let eprintln: String -> () = lam s.
  fileWriteString fileStderr (join [s, "\n"]);
  flushStderr()

let print: String -> () = lam s.
  fileWriteString fileStdout s;
  flushStdout()

let println: String -> () = lam s.
  fileWriteString fileStdout (join [s, "\n"]);
  flushStdout()

let rpcprint: String -> () = lam value.
  let len = addi 1 (length value) in
  println (join ["Content-Length: ", int2string len, "\r\n\r\n", value])

-- END IO --

-- BEGIN JSON --

let jsonKeyObject: [(String, JsonValue)] -> JsonValue = lam content.
  JsonObject (
    mapFromSeq cmpString content
  )

-- END JSON --