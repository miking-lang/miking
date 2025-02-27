include "./methods.mc"

-- This system prunes LSP messages based on some simple rules.
-- E.g. if a file is closed, we remove all messages related to that file.
-- This is also where we handle the `CancelRequest` message.

type MessagePruningEnvironment = {
  cancelled: Map Int Bool,
  closedFiles: Map String Bool,
  overwrittenDidChange: Map String Bool
}

recursive let pruneMessages: MessagePruningEnvironment -> use LSP in [MessageWithContext] -> [MessageWithContext] =
  lam environment. lam messages.
    match messages with [message] ++ messages then
      use LSP in
      switch (message.id, message.message)
        case (_, CancelRequest { id = id }) then
          -- When cancelling a request, we remove the message with the same id
          -- The `CancelRequest` will during execution respond with a
          -- `ErrorCodes.RequestCancelled=32800` error, satisfying the LSP JSON-RPC spec.
          let environment = {
            environment with
            cancelled = mapInsert id true environment.cancelled
          } in
          concat [message] (pruneMessages environment messages)
        case (Some id, _) then
          let messages = pruneMessages environment messages in
          match mapLookup id environment.cancelled with Some _ then
            messages
          else
            concat [message] messages
        case (_, DidClose { uri = uri }) then
          let environment = {
            environment with
            closedFiles = mapInsert uri true environment.closedFiles
          } in
          concat [message] (pruneMessages environment messages)
        case (_, DidOpen { uri = uri }) then
          match mapLookup uri environment.closedFiles with Some _ then
            pruneMessages environment messages
          else
            concat [message] (pruneMessages environment messages)
        case (_, DidChange { uri = uri }) then
          -- When a `DidChange` notification is received, we check if we have already received one for the same URI.
          -- If we have, we don't include this one, as it has been overwritten (we are in a reversed message array).
          -- If we haven't, we include it and mark the URI as having received a `DidChange` notification.
          match mapLookup uri environment.overwrittenDidChange with Some _ then
            pruneMessages environment messages
          else
            let environment = {
              environment with
              overwrittenDidChange = mapInsert uri true environment.overwrittenDidChange
            } in
            concat [message] (pruneMessages environment messages)
        case (_, _) then
          concat [message] (pruneMessages environment messages)
      end
    else
      messages
end

let pruneMessages: use LSP in [MessageWithContext] -> [MessageWithContext] =
  lam messages.
    let messages = reverse messages in
    let environment: MessagePruningEnvironment = {
      cancelled = mapEmpty subi,
      overwrittenDidChange = mapEmpty cmpString,
      closedFiles = mapEmpty cmpString
    } in
    reverse (pruneMessages environment messages)