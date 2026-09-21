include "common.mc"
include "json.mc"
include "./utils.mc"

type RPCRequest = {
  method: String,
  params: Map String JsonValue,
  id: Option Int
}

type RPCError = {
  code: Int,
  message: String,
  data: JsonValue
}

type RPCResult
con RPCSuccess : JsonValue -> RPCResult
con RPCFailure : RPCError  -> RPCResult

type RPCResponse = {
  result: RPCResult,
  id: Int
}

let getContentLength: String -> Int = lam header.
  match header with "Content-Length: " ++ len ++ "\n" then
    string2int len
  else
    error "The JSON-RPC header could not be read, this shouldn't happen!"

let getRPCRequest: JsonValue -> Option RPCRequest = lam request.
  match request with JsonObject request in
  let lookup = (flip mapLookup) request in
  let id = match lookup "id" with Some JsonInt id then Some id else None () in
  match (lookup "method", lookup "params") with (Some JsonString method, Some JsonObject params) then
    Some { method = method, params = params, id = id }
  else
    None ()
