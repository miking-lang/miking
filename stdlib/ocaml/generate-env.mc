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

let emptyGenerateEnv = use MExprCmpClosed in {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp cmpType),
  aliases = mapEmpty nameCmp,
  exts = mapEmpty nameCmp
}

let objRepr = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.repr"}) t
let objMagic = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.magic"}) t

let ocamlTypedFields = lam fields : Map SID Type.
  mapMap (lam. tyunknown_) fields
