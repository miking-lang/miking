include "name.mc"
include "stringid.mc"
include "ocaml/external-includes.mc"
include "mexpr/cmp.mc"

type GenerateEnv = {
  constrs : Map Name (use Ast in Type),
  records : Map (Map SID (use Ast in Type)) Name,
  exts : Map Name [ExternalImpl]
}

let emptyGenerateEnv = use MExprCmp in {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp cmpType),
  exts = mapEmpty nameCmp
}

let objRepr = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.repr"}) t
let objMagic = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.magic"}) t

let ocamlTypedFields = lam fields : Map SID (use Ast in Type).
  mapMap (lam. tyunknown_) fields
