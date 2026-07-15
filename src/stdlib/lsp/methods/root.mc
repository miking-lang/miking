include "../json-rpc.mc"

lang LSPRoot
  syn Message =

  sem getMessage: RPCRequest -> String -> Message
end
