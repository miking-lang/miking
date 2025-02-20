include "ext/file-ext.mc"

-- returns Option content if the requested number of bytes could be read
-- otherwise, None is returned
recursive
  let readBytesBuffered : ReadChannel -> Int -> Option [Int] =
    lam rc. lam len. switch fileReadBytes rc len
      case Some s then (
        let actualLength = length s in
        if eqi actualLength len then Some s
        else match readBytesBuffered rc (subi len actualLength)
          with Some s2 then Some (join [s, s2])
          else None ()
      )
      case None () then None ()
    end
  end

let stripUriProtocol = lam uri. match uri
  with "file://" ++ rest then rest
  else uri
