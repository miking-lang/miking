include "name.mc"
include "stringid.mc"
include "ocaml/external-includes.mc"
include "mexpr/cmp.mc"

type GenerateEnv = {
  constrs : Map Name Type,
  records : Map (Map SID Type) Name,
  aliases : Map Name Type,
  exts : Map Name [ExternalImpl]
}

let _emptyGenerateEnv = use MExprCmp in {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp cmpType),
  aliases = mapEmpty nameCmp,
  exts = mapEmpty nameCmp
}
