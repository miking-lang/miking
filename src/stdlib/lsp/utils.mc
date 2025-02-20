include "ext/file-ext.mc"

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

let stripUriProtocol = lam uri. match uri
  with "file://" ++ rest then rest
  else uri
