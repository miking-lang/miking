include "./root.mc"

lang LSPUnknownMethod = LSPRoot
  syn Message =
  | UnknownMethod {
    method: String
  }

  sem getMessage request =
  | method ->
    UnknownMethod {
      method = method
    }
end
