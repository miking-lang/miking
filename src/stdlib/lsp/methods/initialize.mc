include "json.mc"
include "fileutils.mc"

include "../utils.mc"
include "./root.mc"

lang LSPInitialize = LSPRoot
  syn Message =
  | Initialized {}
  | Initialize {
    processId: Option Int,
    locale: Option String,
    rootPath: Option String,
    rootUri: Option String,
    initializationOptions: Option JsonValue,
    trace: Option String -- 'off' | 'messages' | 'verbose'
  }

  sem getMessage request =
  | "initialized" ->
    Initialized {}
  | "initialize" ->
    let getParam = (flip mapLookup) request.params in

    let processId = match getParam "processId" with JsonInt processId then Some processId else None () in
    let locale = match getParam "locale" with JsonString locale then Some locale else None () in
    let rootPath = match getParam "rootPath" with JsonString rootPath then Some rootPath else None () in
    let rootUri = match getParam "rootUri" with JsonString rootUri then Some rootUri else None () in
    let initializationOptions = getParam "initializationOptions" in
    let trace = match getParam "trace" with JsonString trace then Some trace else None () in

    Initialize {
      processId = processId,
      locale = locale,
      rootPath = optionMap stripUriProtocol rootPath,
      rootUri = optionMap stripUriProtocol rootUri,
      initializationOptions = initializationOptions,
      trace = trace
    }
end
