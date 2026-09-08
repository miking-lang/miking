-- Lets the MLang loader parse `.mc` files with the native MCore parser (`parser/parser.mc`).

include "mlang/loader.mc"
include "mlang/ast.mc"
include "parser/parser.mc"
include "common.mc"
include "result.mc"
include "basic-types.mc"
include "seq.mc"
include "option.mc"
include "mexpr/info.mc"

lang NativeParserLoader = MLangLoader + MLangParser
  sem parseNativeMLangFile : String -> Result () (Info, String) MLangProgram
  sem parseNativeMLangFile = | path ->
    let src = readFile path in
    let cur = nextToken {pos = initPos path, str = src} in
    switch result.consume (parseProgram cur)
    case (_, Right (prog, _)) then result.ok prog
    -- The native parser reports errors as functions from the source
    -- string to the message, so that a message may quote the source it
    -- refers to; the loader wants them already applied.
    case (_, Left errs) then
      foldl1 result.withAnnotations (map (lam e. result.err (e src)) errs)
    end

  sem enableNativeParser : Loader -> Loader
  sem enableNativeParser = | loader ->
    if hasHook (lam x. match x with NativeParserHook _ then true else false) loader
    then loader
    else addHook loader (NativeParserHook {parse = parseNativeMLangFile})
end
