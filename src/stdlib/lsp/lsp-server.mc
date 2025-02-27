include "json.mc"

include "./json-rpc.mc"
include "./methods.mc"
include "./prune.mc"

let sendNotification: JsonValue -> () =
  lam notification.
    let jsonValue = json2string notification in
    eprintln (join [
      "Sending notification\n\n",
      jsonValue,
      "\n\n"
    ]);
    rpcprint jsonValue

let executeRequest: use LSPRoot in LSPStartParameters -> LSPEnvironment -> use LSP in Message -> LSPEnvironment =
  lam parameters. lam environment. lam message.

    let executionContext: use LSPRoot in LSPExecutionContext = {
      parameters = parameters,
      environment = environment,
      sendNotification = sendNotification
    } in

    let result = use LSP in execute executionContext message in

    (
      match result.response with Some response then
        eprintln "Responding to request\n";
        eprintln (pprintjson2string response);
        eprintln "";
        rpcprint (json2string response)
      else
        eprintln ""
    );

    result.environment

let executeRequests: use LSPRoot in LSPStartParameters -> LSPEnvironment -> [String] -> LSPEnvironment =
  lam parameters. lam environment. lam bodies.
    let debugPrintMessages = lam messages.
      let messages = map
        (lam x. join [x.method, ":", match x.id with Some id then int2string id else "?"])
        messages
      in
      strJoin ", " messages
    in

    if leqi (length bodies) 0 then
      environment
    else
      let messages = filterMap (getMessage parameters.options) bodies in

      eprintln (join [
        "Received ",
        int2string (length messages),
        " requests: [",
        debugPrintMessages messages,
        "]"
      ]);

      let messages = if parameters.options.pruneMessages
        then pruneMessages messages
        else messages
      in

      eprintln (join [
        "Executing ",
        int2string (length messages),
        " requests (",
        int2string (subi (length bodies) (length messages)),
        " pruned): [",
        debugPrintMessages messages,
        "]"
      ]);

      let messages = map (lam message. message.message) messages in
      reduce (executeRequest parameters) environment messages

recursive let readJsonRPC: use LSPRoot in LSPStartParameters -> LSPEnvironment -> [String] -> () =
  lam parameters. lam environment. lam bufferedRequests.
    let environment = executeRequests parameters environment bufferedRequests in
    let bufferedRequests = [] in
    let state = switch fileReadLine fileStdin
      case None _ then error "LSP client closed stdout"
      case Some header then
        -- We add 2 to the content length to account for the newline characters
        let contentHeaderLength = addi (getContentLength header) 2 in
        switch readBytesBuffered fileStdin contentHeaderLength
          case None _ then error "LSP client closed stdout"
          case Some body then
            let asciiBody = map int2char body in
            let bufferedRequests = concat bufferedRequests [asciiBody] in
            (environment, bufferedRequests)
        end
    end in

    match state with (environment, bufferedRequests) in
    readJsonRPC parameters environment bufferedRequests
end

let startLSPServer: use LSPRoot in LSPStartParameters -> () =
  lam parameters.
    let environment: use LSPRoot in LSPEnvironment = {
      files = mapEmpty cmpString,
      typeSymbols = mapEmpty subi,
      options = parameters.options,
      rootUri = None ()
    } in
    readJsonRPC parameters environment []